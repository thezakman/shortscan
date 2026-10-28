package shortscan

import (
	"encoding/xml"
	"testing"
)

// a realistic IIS WebDAV multistatus with the D: prefix, mixed files and a collection.
const sampleMultistatus = `<?xml version="1.0" encoding="utf-8"?>
<D:multistatus xmlns:D="DAV:">
  <D:response>
    <D:href>http://host/app/lifttest/</D:href>
    <D:propstat><D:prop><D:displayname>lifttest</D:displayname>
      <D:resourcetype><D:collection/></D:resourcetype></D:prop>
      <D:status>HTTP/1.1 200 OK</D:status></D:propstat>
  </D:response>
  <D:response>
    <D:href>http://host/app/lifttest/AdministratorNotes.txt</D:href>
    <D:propstat><D:prop><D:displayname>AdministratorNotes.txt</D:displayname>
      <D:resourcetype/></D:prop></D:propstat>
  </D:response>
  <D:response>
    <D:href>http://host/app/lifttest/SecretAdminPanel2026/</D:href>
    <D:propstat><D:prop><D:displayname>SecretAdminPanel2026</D:displayname>
      <D:resourcetype><D:collection/></D:resourcetype></D:prop></D:propstat>
  </D:response>
</D:multistatus>`

func TestDavMultistatusParse(t *testing.T) {
	var ms davMultistatus
	if err := xml.Unmarshal([]byte(sampleMultistatus), &ms); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	if len(ms.Responses) != 3 {
		t.Fatalf("want 3 responses, got %d", len(ms.Responses))
	}
	if got := ms.Responses[1].Propstats[0].Prop.Displayname; got != "AdministratorNotes.txt" {
		t.Errorf("displayname = %q", got)
	}
	if !isCollection(ms.Responses[2]) {
		t.Errorf("SecretAdminPanel2026 should be a collection")
	}
	if isCollection(ms.Responses[1]) {
		t.Errorf("AdministratorNotes.txt should not be a collection")
	}
}

// href-only servers (no displayname) must still yield the child name via the basename.
func TestChildNameHrefFallback(t *testing.T) {
	r := davResponse{Href: "http://host/app/Some%20File.aspx"}
	if got := childName(r, requestPath(r.Href)); got != "Some File.aspx" {
		t.Errorf("href fallback = %q, want %q", got, "Some File.aspx")
	}
	r2 := davResponse{
		Href:      "http://host/app/x.txt",
		Propstats: []davPropstat{{Prop: davProp{Displayname: "preferred.txt"}}},
	}
	if got := childName(r2, requestPath(r2.Href)); got != "preferred.txt" {
		t.Errorf("displayname preference = %q", got)
	}
}

func TestPathsEqualSelfExclusion(t *testing.T) {
	if !pathsEqual("/app/lifttest/", "/app/lifttest") {
		t.Errorf("trailing slash should not matter")
	}
	if pathsEqual("/app/lifttest/", "/app/lifttest/child") {
		t.Errorf("child must not equal self")
	}
}

func TestWebdavSensitive(t *testing.T) {
	cases := []struct {
		name    string
		coll    bool
		flagged bool
	}{
		{"web.config", false, true},
		{"appsettings.config", false, true},
		{"backup.bak", false, true},
		{"db.sql", false, true},
		{"server.pem", false, true},
		{"archive.zip", false, true},
		{"bin", true, true},
		{"App_Data", true, true},
		{"images", true, false},
		{"index.html", false, false},
		{"style.css", false, false},
	}
	for _, c := range cases {
		got := webdavSensitive(c.name, c.coll) != ""
		if got != c.flagged {
			t.Errorf("webdavSensitive(%q, coll=%v) flagged=%v, want %v", c.name, c.coll, got, c.flagged)
		}
	}
}

// TestSensitiveReasonForRecoveredFiresOnInferred guards against the bug where the
// [SENSITIVE] tag in the main resolved short-name output was gated on resolvedLong
// alone: request-filtered extensions (web.config, .cs, .mdf, …) can only ever be
// recovered via the wordlist-inferred matchType (see isRequestFilteredName), never
// HTTP-confirmed, so that gate made the tag dead code for its highest-value targets.
func TestSensitiveReasonForRecoveredFiresOnInferred(t *testing.T) {
	cases := []struct {
		fnr       string
		matchType string
		flagged   bool
	}{
		{"web.config", "wordlist-inferred", true},
		{"appsettings.config", "wordlist-inferred", true},
		{"backup.bak", "reference", true},
		{"archive.zip", "checksum-mask", true},
		{"index.html", "wordlist", false},
		{"", "wordlist-inferred", false},
		// A bare short-name echo still carries its truncated 8.3 extension
		// (e.g. "WEBCON~1.CON"), which is not reliable classification input.
		{"WEBCON~1.CON", "short-name", false},
	}
	for _, c := range cases {
		got := sensitiveReasonForRecovered(c.fnr, c.matchType) != ""
		if got != c.flagged {
			t.Errorf("sensitiveReasonForRecovered(%q, %q) flagged=%v, want %v", c.fnr, c.matchType, got, c.flagged)
		}
	}
}

func TestResolvesAlias(t *testing.T) {
	aliases := []confirmedAlias{
		{file: "admini", ext: "txt"},
		{file: "databa", ext: "con"},
		{file: "secret", ext: ""}, // directory alias (no ext)
	}
	cases := []struct {
		name string
		coll bool
		want string
	}{
		{"AdministratorNotes.txt", false, "ADMINI~1.TXT"},
		{"DatabaseCredentials.config", false, "DATABA~1.CON"},
		{"SecretAdminPanel2026", true, "SECRET~1"},
		{"Unrelated.txt", false, ""}, // prefix mismatch
	}
	for _, c := range cases {
		if got := resolvesAlias(c.name, c.coll, aliases); got != c.want {
			t.Errorf("resolvesAlias(%q) = %q, want %q", c.name, got, c.want)
		}
	}
}

func TestIsDotSegment(t *testing.T) {
	cases := []struct {
		name string
		want bool
	}{
		{"", false},
		{".", true},
		{"..", true},
		{"...", false},
		{"secret", false},
		{".hidden", false},
	}
	for _, c := range cases {
		if got := isDotSegment(c.name); got != c.want {
			t.Errorf("isDotSegment(%q) = %v, want %v", c.name, got, c.want)
		}
	}
}

func TestValidChildName(t *testing.T) {
	cases := []struct {
		name string
		want bool
	}{
		{"", false},
		{".", false},
		{"..", false},
		{"secret", true},
		{"Some File.aspx", true},
		{"a/b", false},
		{"a\\b", false},
		{"a:b", false},
	}
	for _, c := range cases {
		if got := validChildName(c.name); got != c.want {
			t.Errorf("validChildName(%q) = %v, want %v", c.name, got, c.want)
		}
	}
}

// A WebDAV server (misconfigured or hostile) reporting ".." as a collection
// child must never reach propfindChildren's output — otherwise --recurse
// would enqueue a URL that climbs out of the directory tree it was pointed
// at, and Scan's visited map (a raw string dedup) would never catch the
// resulting "../", "../../", … chain.
func TestPropfindChildrenRejectsDotSegments(t *testing.T) {
	const multistatus = `<?xml version="1.0" encoding="utf-8"?>
<D:multistatus xmlns:D="DAV:">
  <D:response>
    <D:href>http://host/app/lifttest/</D:href>
    <D:propstat><D:prop><D:displayname>..</D:displayname>
      <D:resourcetype><D:collection/></D:resourcetype></D:prop></D:propstat>
  </D:response>
  <D:response>
    <D:href>http://host/app/lifttest/child/</D:href>
    <D:propstat><D:prop><D:displayname>child</D:displayname>
      <D:resourcetype><D:collection/></D:resourcetype></D:prop></D:propstat>
  </D:response>
</D:multistatus>`
	var ms davMultistatus
	if err := xml.Unmarshal([]byte(multistatus), &ms); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	selfPath := requestPath("http://host/app/lifttest/")
	var names []string
	for _, r := range ms.Responses {
		hrefPath := requestPath(r.Href)
		if pathsEqual(hrefPath, selfPath) {
			continue
		}
		name := childName(r, hrefPath)
		if !validChildName(name) {
			continue
		}
		names = append(names, name)
	}
	if len(names) != 1 || names[0] != "child" {
		t.Fatalf("want only [child], got %v", names)
	}
}

// The enriched PROPFIND pulls size + last-modified for free; the lift uses them
// to tell a stubbed hidden .config from one that actually holds secrets.
func TestChildMetaAndFormat(t *testing.T) {
	const ms = `<?xml version="1.0"?>
<D:multistatus xmlns:D="DAV:">
  <D:response>
    <D:href>http://host/app/web.config</D:href>
    <D:propstat><D:prop><D:displayname>web.config</D:displayname>
      <D:resourcetype/>
      <D:getcontentlength>4096</D:getcontentlength>
      <D:getlastmodified>Thu, 13 Aug 2026 01:36:41 GMT</D:getlastmodified></D:prop></D:propstat>
  </D:response>
  <D:response>
    <D:href>http://host/app/sub/</D:href>
    <D:propstat><D:prop><D:displayname>sub</D:displayname>
      <D:resourcetype><D:collection/></D:resourcetype>
      <D:getcontentlength>0</D:getcontentlength></D:prop></D:propstat>
  </D:response>
</D:multistatus>`
	var doc davMultistatus
	if err := xml.Unmarshal([]byte(ms), &doc); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	size, mod := childMeta(doc.Responses[0])
	if size != "4096" {
		t.Errorf("size = %q, want 4096", size)
	}
	file := davChild{name: "web.config", size: size, modified: mod}
	if got := formatChildMeta(file); got != "(4.0 KB, 13 Aug 2026)" {
		t.Errorf("formatChildMeta(file) = %q", got)
	}
	// A collection must not render a size annotation.
	dir := davChild{name: "sub", collection: true, size: "0"}
	if got := formatChildMeta(dir); got != "" {
		t.Errorf("formatChildMeta(dir) = %q, want empty", got)
	}
	if got := compactDavDate("Thu, 13 Aug 2026 01:36:41 GMT"); got != "13 Aug 2026" {
		t.Errorf("compactDavDate = %q", got)
	}
}

func TestDrainConfirmedAliases(t *testing.T) {
	ac := &attackConfig{}
	recordConfirmedAlias(ac, baseRequest{file: "REPORT", ext: ".ASP"})
	recordConfirmedAlias(ac, baseRequest{file: "SECRET", ext: ""})
	got := drainConfirmedAliases(ac)
	if len(got) != 2 {
		t.Fatalf("want 2 drained, got %d", len(got))
	}
	if got[0].file != "report" || got[0].ext != "asp" {
		t.Errorf("normalisation: %+v", got[0])
	}
	if again := drainConfirmedAliases(ac); len(again) != 0 {
		t.Errorf("drain should reset, got %d", len(again))
	}
}
