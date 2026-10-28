package shortscan

import (
	"encoding/xml"
	"net/http"
	nurl "net/url"
	"path"
	"sort"
	"strconv"
	"strings"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
	"github.com/thezakman/shortscan/pkg/shortutil"
)

// WebDAV full-name lift.
//
// The 8.3 tilde oracle is information-bounded to 6+3 characters (a confirmed alias
// like SECRET~1.ASP does not, on its own, reveal the rest of the long name), and a
// fully patched IIS refuses to serve the alias itself (404.0 canonical mismatch).
// But when the target announces WebDAV — a common misconfiguration, the module is
// installed on many legacy/collab/file-serving IIS hosts — an anonymous
// PROPFIND Depth:1 on an *allowed* directory returns the FULL long names of its
// immediate children as <D:displayname>/<D:href>. That defeats the 6+3 truncation
// and, crucially, also discloses child names that requestFiltering hides from a
// direct GET (web.config, bin, App_Data, *.bak/*.old/*.config).
//
// Bounded, and honest about it: Depth:1 lists ONE directory level (Depth:infinity is
// 403 by default); a PROPFIND aimed directly at a hidden segment (/bin, /App_Data) is
// itself 404 (requestFiltering matches the request URL); and the CONTENT of a
// blocked-extension file stays blocked. So this recovers NAMES, not blocked content.
// Live-confirmed on a patched Windows 11 / IIS 10 + WebDAV lab (2026-08).
// The technique is WebDAV listing (prior art); the value here is first-class
// integration — recovering full names for the scan and flagging the hidden-name
// disclosure — not a new parser primitive.

// confirmedAlias is the lowercased 6-char prefix + 3-char extension of a short name
// the scan confirmed. runWebDAVLift joins these against PROPFIND-recovered long names
// so a lift can announce "SECRET~1.ASP -> SecretConfiguration.aspx".
type confirmedAlias struct{ file, ext string }

// maxWebDAVLiftChildren caps how many PROPFIND Depth:1 children a single
// directory lift acts on — both for the printed listing and for what
// --recurse queues, so a child past the cap is never silently scanned
// without first being shown as found.
const maxWebDAVLiftChildren = 500

// recordConfirmedAlias is called from enumerate() at each confirmed short name when
// --webdav is set, so the per-directory lift can tie recovered names back to findings.
// The store is per-scan (on attackConfig) so a --parallel run never mixes hosts.
func recordConfirmedAlias(ac *attackConfig, br baseRequest) {
	ac.enumMutex.Lock()
	ac.confirmedAliases = append(ac.confirmedAliases, confirmedAlias{
		file: strings.ToLower(br.file),
		ext:  strings.ToLower(strings.TrimPrefix(br.ext, ".")),
	})
	ac.enumMutex.Unlock()
}

func drainConfirmedAliases(ac *attackConfig) []confirmedAlias {
	ac.enumMutex.Lock()
	defer ac.enumMutex.Unlock()
	out := append([]confirmedAlias(nil), ac.confirmedAliases...)
	ac.confirmedAliases = nil
	return out
}

// DAV multistatus parsing. Tags are unqualified so they match by local name across
// the various namespace prefixes servers emit (D:, d:, lp1:, a:, …).
type davMultistatus struct {
	XMLName   xml.Name      `xml:"multistatus"`
	Responses []davResponse `xml:"response"`
}

type davResponse struct {
	Href      string        `xml:"href"`
	Propstats []davPropstat `xml:"propstat"`
}

type davPropstat struct {
	Prop davProp `xml:"prop"`
}

type davProp struct {
	Displayname   string       `xml:"displayname"`
	Resourcetype  davResources `xml:"resourcetype"`
	Contentlength string       `xml:"getcontentlength"`
	Lastmodified  string       `xml:"getlastmodified"`
	Contenttype   string       `xml:"getcontenttype"`
}

type davResources struct {
	Collection *struct{} `xml:"collection"`
}

type davChild struct {
	name       string
	collection bool
	size       string // getcontentlength, as advertised ("" if absent)
	modified   string // getlastmodified, trimmed to a date if possible
}

// runWebDAVLift is a post-scan step: if the scanned directory announces WebDAV, it
// PROPFIND Depth:1s the directory and reports the recovered long names, joining them
// to the confirmed 8.3 aliases and flagging requestFiltering-hidden names.
func runWebDAVLift(hc *http.Client, st *httpStats, ac *attackConfig, rawURL string) {
	aliases := drainConfirmedAliases(ac)
	if !args.WebDAV {
		return
	}
	dir := stripIndexAllocation(rawURL)
	if !strings.HasSuffix(dir, "/") {
		dir += "/"
	}

	// 1. Announce check — OPTIONS must advertise DAV, or the PROPFIND is pointless noise.
	res, err := fetch(hc, st, "OPTIONS", dir)
	if err != nil || res == nil {
		return
	}
	dav := res.Header.Get("DAV")
	msAuthor := res.Header.Get("MS-Author-Via")
	if dav == "" && !strings.Contains(strings.ToUpper(msAuthor), "DAV") {
		// "lift skipped" is a non-finding (DAV:no already shows in the fingerprint
		// line); keep it out of the default output — verbose only.
		log.Debug("[WEBDAV] not advertised (no DAV header) — lift skipped")
		return
	}

	// 2. PROPFIND Depth:1 for the immediate children.
	children, code, err := propfindChildren(hc, st, dir)
	if err != nil {
		return
	}
	if len(children) == 0 {
		if args.Output == "human" && !bulkCompact() {
			beginSection(ac)
			printHuman(color.HiBlackString("[WEBDAV] DAV: %s advertised, but PROPFIND gave %d — no listable children (auth/authoring-rule restricted)", dav, code))
		}
		return
	}

	// Truncate once, here, so the displayed listing and the --recurse queue
	// agree on exactly the same set — a child past the cap must not be silently
	// scanned without ever being shown as found.
	truncated := false
	if len(children) > maxWebDAVLiftChildren {
		children = children[:maxWebDAVLiftChildren]
		truncated = true
	}

	// Names already recovered inline (enumeration/reference/sibling) shouldn't be re-listed.
	recovered := map[string]bool{}
	if ac != nil {
		ac.autocompleteMutex.Lock()
		for k := range ac.foundFiles {
			recovered[strings.ToLower(strings.TrimPrefix(k, "/"))] = true
		}
		ac.autocompleteMutex.Unlock()
	}
	reportWebDAVLift(ac, dir, dav, children, truncated, aliases, recovered)

	if ac != nil {
		for _, c := range children {
			candidatePath := pathEscape(c.name)
			if c.collection {
				// --recurse: a PROPFIND collection entry is a real subdirectory,
				// whether or not the primary short-name pipeline ever resolved an
				// 8.3 alias for it. Queue it the same way markResolvedFile queues
				// an extensionless recovered path (recovery.go) — Scan()'s normal
				// pre-flight re-verifies it with the short-name oracle before any
				// real work is spent, so this is as safe as the existing
				// recursion source, just fed by PROPFIND instead of the oracle.
				if args.Recurse {
					ac.foundDirectories[candidatePath] = struct{}{}
				}
				continue
			}
			// A recovered file is real content too: record it so other recovery
			// paths don't re-probe it, and seed the reference crawler so a
			// PROPFIND-recovered .html/.js/.json/.xml gets its own content
			// scraped for further leads — the same propagation directory
			// children get above, just for files.
			ac.foundFiles[foundFileKey(candidatePath)] = struct{}{}
			rememberReferenceSeed(ac, dir, candidatePath)
			// A PROPFIND-recovered sensitive file (web.config, *.config,
			// appsettings.json, keys, backups) is blocked for a direct GET by
			// request filtering — queue it for the post-scan cookieless
			// source-probe (dir-split + extension-split), which discloses it on an
			// aggressive-cookieless / unpatched host. Runs under --auto/--full/--index.
			if _, ok := sensitiveDisclosureLabel(c.name); ok && ac.sourceHits != nil {
				recordSourceHit(ac, sourceHit{probeURL: dir + candidatePath, name: c.name, how: "webdav-lift"})
			}
		}
	}
}

// propfindChildren issues an anonymous PROPFIND Depth:1 and returns the immediate
// children (the collection's own entry excluded). Depth is pinned to 1 on purpose —
// Depth:infinity is both commonly 403 and needlessly heavy.
func propfindChildren(hc *http.Client, st *httpStats, dir string) ([]davChild, int, error) {
	const propfindDoc = `<?xml version="1.0" encoding="utf-8"?>` +
		`<D:propfind xmlns:D="DAV:"><D:prop><D:displayname/><D:resourcetype/>` +
		`<D:getcontentlength/><D:getlastmodified/><D:getcontenttype/></D:prop></D:propfind>`
	res, body, err := fetchBodyWithHeaders(hc, st, "PROPFIND", dir, propfindDoc, 1<<20, map[string]string{
		"Depth":        "1",
		"Content-Type": "text/xml; charset=utf-8",
	})
	if err != nil || res == nil {
		return nil, 0, err
	}
	code := res.StatusCode
	if code != http.StatusMultiStatus { // 207
		return nil, code, nil
	}

	var ms davMultistatus
	if err := xml.Unmarshal(body, &ms); err != nil {
		return nil, code, err
	}

	selfPath := requestPath(dir)
	seen := make(map[string]struct{})
	var out []davChild
	for _, r := range ms.Responses {
		hrefPath := requestPath(r.Href)
		// Skip the collection's own entry (self).
		if pathsEqual(hrefPath, selfPath) {
			continue
		}
		name := childName(r, hrefPath)
		if !validChildName(name) {
			continue
		}
		key := strings.ToLower(name)
		if _, dup := seen[key]; dup {
			continue
		}
		seen[key] = struct{}{}
		size, modified := childMeta(r)
		out = append(out, davChild{name: name, collection: isCollection(r), size: size, modified: modified})
	}
	sort.Slice(out, func(i, j int) bool { return strings.ToLower(out[i].name) < strings.ToLower(out[j].name) })
	return out, code, nil
}

// childName prefers <displayname>; it falls back to the basename of the href, which
// every compliant server returns. hrefPath is already decoded by requestPath, so no
// further unescaping happens here (re-unescaping would corrupt a name containing a
// literal '%' followed by two hex-digit characters).
func childName(r davResponse, hrefPath string) string {
	for _, ps := range r.Propstats {
		if dn := strings.TrimSpace(ps.Prop.Displayname); dn != "" {
			return dn
		}
	}
	base := path.Base(strings.TrimRight(hrefPath, "/"))
	if base == "." || base == "/" || base == "" {
		return ""
	}
	return base
}

// childMeta extracts the advertised size and last-modified date for a child, if
// the server returned them. These come free in the same PROPFIND and are the
// point of the enrichment: for a requestFiltering-hidden name (a .config, a
// .bak) the size is what separates a stub from real secrets, and no GET is
// possible to learn it (the direct GET is 404). Size is only meaningful for
// files; a collection's getcontentlength is dropped.
func childMeta(r davResponse) (string, string) {
	var size, modified string
	for _, ps := range r.Propstats {
		if size == "" {
			size = strings.TrimSpace(ps.Prop.Contentlength)
		}
		if modified == "" {
			modified = strings.TrimSpace(ps.Prop.Lastmodified)
		}
	}
	return size, modified
}

// formatChildMeta renders a compact "(size, date)" annotation for a file child.
// Collections have no meaningful content length, so they get nothing.
func formatChildMeta(c davChild) string {
	if c.collection {
		return ""
	}
	var parts []string
	if c.size != "" {
		if n, err := strconv.Atoi(c.size); err == nil {
			parts = append(parts, formatBytes(n))
		} else {
			parts = append(parts, c.size+" B")
		}
	}
	if d := compactDavDate(c.modified); d != "" {
		parts = append(parts, d)
	}
	if len(parts) == 0 {
		return ""
	}
	return "(" + strings.Join(parts, ", ") + ")"
}

// compactDavDate reduces an RFC1123 getlastmodified ("Thu, 13 Aug 2026 01:36:41
// GMT") to a glanceable "13 Aug 2026"; unknown formats pass through unchanged.
func compactDavDate(s string) string {
	if f := strings.Fields(s); len(f) >= 4 {
		return strings.Join(f[1:4], " ")
	}
	return strings.TrimSpace(s)
}

// validChildName rejects a PROPFIND-reported child name before it can become a
// URL path segment. <D:displayname> is server-controlled and unescaped (unlike
// the href fallback, it is never run through path.Base), so a dot-segment here
// would otherwise let a directory escape the tree --recurse was pointed at, and
// a name repeating "." or ".." across levels would never dedup in Scan's
// visited map — same guard an untrusted segment gets in references.go and
// aliasprobe.go.
func validChildName(name string) bool {
	return name != "" && !isDotSegment(name) && !strings.ContainsAny(name, "\\/:*?\"<>|")
}

func isCollection(r davResponse) bool {
	for _, ps := range r.Propstats {
		if ps.Prop.Resourcetype.Collection != nil {
			return true
		}
	}
	return false
}

// requestPath reduces an absolute or relative href to a clean, decoded path.
// url.Parse already percent-decodes into u.Path, so no further unescaping is
// applied here — re-unescaping an already-decoded path corrupts any name whose
// true (singly-decoded) form contains a literal '%' followed by two hex-digit
// characters, e.g. "50%A9 report.txt" decoding again into a raw non-UTF8 byte.
func requestPath(raw string) string {
	if u, err := nurl.Parse(raw); err == nil {
		return u.Path
	}
	return raw
}

func pathsEqual(a, b string) bool {
	return strings.TrimRight(a, "/") == strings.TrimRight(b, "/")
}

// reportWebDAVLift prints the recovered long names, marking hidden-name disclosures
// and, when a recovered name's computed 8.3 form matches one the scan confirmed, the
// alias it resolves.
func reportWebDAVLift(ac *attackConfig, dir, dav string, children []davChild, truncated bool, aliases []confirmedAlias, recovered map[string]bool) {
	// Dedup: don't re-list names already recovered inline (enumeration/reference/sibling);
	// only surface genuinely-new names plus every requestFiltering-hidden one (web.config,
	// /bin, *.bak …) — the unique value of the lift.
	shown := make([]davChild, 0, len(children))
	dup := 0
	for _, c := range children {
		if !c.collection && webdavSensitive(c.name, c.collection) == "" && recovered[strings.ToLower(c.name)] {
			dup++
			continue
		}
		shown = append(shown, c)
	}

	if args.Output == "human" {
		if len(shown) == 0 {
			beginSection(ac)
			printHuman(color.HiBlackString("[WEBDAV-LIFT] %s via PROPFIND — all already known", pluralCount(len(children), "name", "names")))
			return
		}
		beginSection(ac)
		if dup > 0 {
			printHuman(color.HiCyanString("[WEBDAV-LIFT] %s via PROPFIND (DAV: %s), +%d known", pluralCount(len(shown), "name", "names"), dav, dup))
		} else {
			printHuman(color.HiCyanString("[WEBDAV-LIFT] %s via PROPFIND (DAV: %s)", pluralCount(len(shown), "name", "names"), dav))
		}
	}

	for _, c := range shown {
		reason := webdavSensitive(c.name, c.collection)
		resolved := resolvesAlias(c.name, c.collection, aliases)
		display := c.name
		if c.collection {
			display += "/"
		}

		if args.Output != "human" {
			rec := map[string]any{
				"type":       "webdav-name-lift",
				"dir":        dir,
				"name":       c.name,
				"collection": c.collection,
			}
			if c.size != "" {
				rec["size"] = c.size
			}
			if c.modified != "" {
				rec["modified"] = c.modified
			}
			if reason != "" {
				rec["hidden_name_disclosure"] = reason
			}
			if resolved != "" {
				rec["resolves_alias"] = resolved
			}
			printJSON(rec)
			continue
		}

		line := "  " + color.HiWhiteString(display)
		if meta := formatChildMeta(c); meta != "" {
			line += " " + color.HiBlackString(meta)
		}
		if resolved != "" {
			line += color.GreenString("  ← resolves 8.3 %s", resolved)
		}
		if reason != "" {
			line += "  " + color.HiRedString("[HIDDEN-NAME] %s", reason)
		}
		printHuman(line)
	}

	if truncated && args.Output == "human" {
		printHuman("  " + color.HiBlackString("… capped at %d entries", maxWebDAVLiftChildren))
	}
}

// resolvesAlias computes the recovered name's 8.3 prefix+ext and reports the matching
// confirmed alias (e.g. "SECRET~1.ASP"), or "" if none matches.
func resolvesAlias(name string, collection bool, aliases []confirmedAlias) string {
	file, ext := splitNameExt(name)
	req, p6, e3 := shortutil.Gen8dot3(file, ext)
	_ = req
	p6l, e3l := strings.ToLower(p6), strings.ToLower(e3)
	for _, a := range aliases {
		if a.file != "" && !strings.HasPrefix(p6l, a.file) {
			continue
		}
		if a.ext != "" && !strings.HasPrefix(e3l, a.ext) {
			continue
		}
		alias := strings.ToUpper(p6) + "~1"
		if e3 != "" {
			alias += "." + strings.ToUpper(e3)
		}
		return alias
	}
	return ""
}

// splitNameExt splits a filename into (name, ext-without-dot) for Gen8dot3. A leading
// dot (dotfile) is treated as part of the name with no extension.
func splitNameExt(name string) (string, string) {
	i := strings.LastIndex(name, ".")
	if i <= 0 {
		return name, ""
	}
	return name[:i], name[i+1:]
}

// webdavSensitive returns a reason string when a recovered child name is one that
// default requestFiltering hides from a direct GET (so its disclosure via PROPFIND is
// itself a finding), or is otherwise high-value loot.
func webdavSensitive(name string, collection bool) string {
	low := strings.ToLower(name)
	if collection {
		if _, ok := dotNetProtectedFolders[low]; ok {
			return "requestFiltering hiddenSegment — direct GET is blocked (404)"
		}
		return ""
	}
	return sensitiveFileReason(low)
}

// sensitiveFileReason returns a short reason string when a (lowercased) filename is
// high-value loot: config/secrets, backups, database dumps, key material, archives,
// logs or source/project files. Shared by the WebDAV name-lift and the main resolved
// short-name output so both flag the same file classes.
func sensitiveFileReason(low string) string {
	if low == "web.config" {
		return "web.config — connection strings / machineKey; blocked for direct GET"
	}
	_, ext := splitNameExt(low)
	switch ext {
	case "config":
		return ".config — likely secrets; blocked for direct GET"
	case "bak", "old", "orig", "save", "swp", "bkp", "backup", "tmp", "temp", "inc", "~":
		return "backup/temp — often full source or secrets"
	case "sql", "mdf", "ldf", "sqlite", "db":
		return "database file/dump"
	case "pem", "key", "pfx", "p12", "kdbx", "jks", "env", "pkcs12":
		return "credential/key material"
	case "zip", "7z", "tar", "gz", "tgz", "rar":
		return "archive — possible source/backup"
	case "log":
		return "log — may leak paths/credentials"
	case "cs", "vb", "csproj", "vbproj", "sln", "asax":
		return "source/project file"
	}
	if strings.HasSuffix(low, "~") {
		return "editor backup — often full source"
	}
	return ""
}

// sensitiveReasonForRecovered returns the [SENSITIVE] annotation reason for a name
// recovery produced for a short-name match, or "" if none applies. It fires for both
// HTTP-confirmed resolutions AND wordlist-inferred ones: many of the highest-value
// extensions (web.config, .cs, .mdf, …) are exactly the ones IIS's requestFiltering
// hides from a direct GET, so recovery can only ever surface them via the
// wordlist-inferred path (see isRequestFilteredName) — they are never HTTP-confirmed.
// Gating on confirmation alone would make the tag dead code for its primary targets.
// It does not fire for a bare short-name alias echo (matchType prefixed "short-name"):
// that name still carries its truncated 8.3 extension, which isn't reliable input for
// classification.
func sensitiveReasonForRecovered(fnr, matchType string) string {
	if fnr == "" || strings.HasPrefix(matchType, "short-name") {
		return ""
	}
	return sensitiveFileReason(strings.ToLower(fnr))
}
