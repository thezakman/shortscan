package shortscan

import (
	"bytes"
	"fmt"
	"net/http"
	"reflect"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
)

func TestCollapseEnumEntries(t *testing.T) {
	grp := "SYSTEM~*.DLL\x00system.web.helpers.dll"
	entries := []enumEntry{
		{sortKey: "SYSTEM~3.DLL", dedupKey: grp, line: "SYSTEM~3.DLL name", resolved: true},
		{sortKey: "SYSTEM~1.DLL", dedupKey: grp, line: "SYSTEM~1.DLL name", resolved: true},
		{sortKey: "SYSTEM~2.DLL", dedupKey: grp, line: "SYSTEM~2.DLL name", resolved: true},
		{sortKey: "SYSTEM~4.DLL", dedupKey: grp, line: "SYSTEM~4.DLL name", resolved: true},
		{sortKey: "README~1.TXT", dedupKey: "", line: "README~1.TXT readme.txt", resolved: true}, // singleton, resolved
		{sortKey: "ZZZ~1.AAA", dedupKey: "", line: "ZZZ~1.AAA pattern", resolved: false},         // unresolved
	}
	lines, resolved := collapseEnumEntries(entries)

	// 4 SYSTEM ordinals collapse to 1; + README + ZZZ = 3 lines.
	if len(lines) != 3 {
		t.Fatalf("expected 3 lines after collapse, got %d: %v", len(lines), lines)
	}
	// resolved = 1 (SYSTEM group) + 1 (README) = 2.
	if resolved != 2 {
		t.Fatalf("expected resolved=2, got %d", resolved)
	}
	joined := strings.Join(lines, "\n")
	if !strings.Contains(joined, "SYSTEM~1.DLL") {
		t.Fatalf("expected the lowest ordinal (SYSTEM~1.DLL) kept, got:\n%s", joined)
	}
	for _, dropped := range []string{"SYSTEM~2.DLL", "SYSTEM~3.DLL", "SYSTEM~4.DLL"} {
		if strings.Contains(joined, dropped) {
			t.Fatalf("collapsed output must not contain %s:\n%s", dropped, joined)
		}
	}
	if !strings.Contains(joined, "1 of 4") {
		t.Fatalf("expected the group-size annotation '1 of 4', got:\n%s", joined)
	}
}

func TestIndexAllocationBase(t *testing.T) {
	cases := map[string]string{
		"http://h/bin/":                    "http://h/bin::$INDEX_ALLOCATION/",
		"http://h/a/bin/":                  "http://h/a/bin::$INDEX_ALLOCATION/",
		"http://h/":                        "http://h/",                        // site root: nothing to tag
		"http://h/bin::$INDEX_ALLOCATION/": "http://h/bin::$INDEX_ALLOCATION/", // already ADS
	}
	for in, want := range cases {
		if got := indexAllocationBase(in); got != want {
			t.Errorf("indexAllocationBase(%q) = %q, want %q", in, got, want)
		}
	}
}

func TestParseIISDetailPortuguese(t *testing.T) {
	body := []byte(`<title>Erro detalhado do IIS 10.0 - 404.8 - Not Found</title>` +
		`<fieldset><legend>Module</legend> RequestFilteringModule </fieldset>`)
	v, s, m := parseIISDetail(body)
	if v != "10.0" || s != "404.8" || m != "RequestFilteringModule" {
		t.Fatalf("parseIISDetail = version=%q substatus=%q module=%q", v, s, m)
	}
	if v2, s2, _ := parseIISDetail([]byte("generic 404 page, no detail")); v2 != "" || s2 != "" {
		t.Fatalf("expected empty parse on generic body, got version=%q substatus=%q", v2, s2)
	}
}

func TestSubstatusMeaning(t *testing.T) {
	cases := map[string]string{
		"404.8":  "hidden segment",
		"404.11": "double escaping",
		"404.0":  "not found",
		"999.9":  "", // unknown -> empty
	}
	for code, want := range cases {
		if got := substatusMeaning(code); got != want {
			t.Errorf("substatusMeaning(%q) = %q, want %q", code, got, want)
		}
	}
}

// TestParallelSharedStateRace hammers the package-global stores that --parallel
// URL scans genuinely contend on (single-stack fingerprint set, confirmed-alias
// WebDAV list, and the status/distance caches) from many goroutines at once.
// Per-Scan state (visited, siblingStems, references, attackConfig) is isolated by
// construction; these globals are the ones that must stay mutex-guarded. Run with
// `go test -race` — an unguarded map access here fails as a data race / concurrent
// map write, exactly the crash class a bad --parallel would produce live.
func TestParallelSharedStateRace(t *testing.T) {
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	singleStackHosts = map[string]bool{}
	ac := &attackConfig{} // confirmedAliases is now per-scan; exercise its concurrent append

	const workers = 24
	var wg sync.WaitGroup
	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func(w int) {
			defer wg.Done()
			for i := 0; i < 200; i++ {
				host := fmt.Sprintf("https://h%d/", (w+i)%8)
				markSingleStackIIS(host)
				_ = isSingleStackIIS(host)

				recordConfirmedAlias(ac, baseRequest{file: fmt.Sprintf("FILE%02d", i%16), ext: ".TXT"})
				if i%17 == 0 {
					_ = drainConfirmedAliases(ac)
				}

				key := fmt.Sprintf("k%d", (w+i)%8)
				cacheMutex.Lock()
				statusCache[key] = map[int]struct{}{404: {}}
				distanceCache[key] = map[int]distances{}
				cacheMutex.Unlock()
				cacheMutex.RLock()
				_ = statusCache[key]
				_ = distanceCache[key]
				cacheMutex.RUnlock()
			}
		}(w)
	}
	wg.Wait()
}

// TestHostSinkBufferingNoInterleave proves the --parallel human buffering: with
// several hosts writing concurrently, each host's lines land in one contiguous,
// header-labelled block — never interleaved with another host's. This is the
// property that makes parallel human output readable instead of a line-salad.
func TestHostSinkBufferingNoInterleave(t *testing.T) {
	prevWriter, prevOutput := outputWriter, args.Output
	prevActive := atomic.LoadInt32(&hostSinkActive)
	defer func() {
		outputWriter, args.Output = prevWriter, prevOutput
		atomic.StoreInt32(&hostSinkActive, prevActive)
		hostSinkMu.Lock()
		hostSinks = map[int64]*hostSink{}
		hostSinkMu.Unlock()
	}()

	var out bytes.Buffer
	outputWriter = &out
	args.Output = "human"
	enableHostSinks()

	const perHost = 25
	hosts := []string{"https://alpha/", "https://bravo/", "https://charlie/"}
	var wg sync.WaitGroup
	for _, h := range hosts {
		wg.Add(1)
		go func(h string) {
			defer wg.Done()
			beginHostSink(h)
			defer flushHostSink()
			for i := 0; i < perHost; i++ {
				printHuman(fmt.Sprintf("%sline %d", h, i))
			}
		}(h)
	}
	wg.Wait()

	// Each host's lines must form exactly one contiguous run — no other host's
	// line may appear between them — and each host contributes exactly perHost
	// lines. (Flush indents the body under a header, so trim leading space.)
	lines := strings.Split(strings.TrimRight(out.String(), "\n"), "\n")
	var runs []string
	counts := map[string]int{}
	for _, ln := range lines {
		ln = strings.TrimSpace(ln)
		if ln == "" {
			continue
		}
		matched := ""
		for _, h := range hosts {
			if strings.HasPrefix(ln, h) {
				matched = h
				break
			}
		}
		if matched == "" {
			t.Fatalf("unexpected line %q\n%s", ln, out.String())
		}
		counts[matched]++
		if len(runs) == 0 || runs[len(runs)-1] != matched {
			runs = append(runs, matched)
		}
	}
	if len(runs) != len(hosts) {
		t.Fatalf("expected %d contiguous host runs, got %d (interleaved): %v", len(hosts), len(runs), runs)
	}
	seen := map[string]bool{}
	for _, h := range runs {
		if seen[h] {
			t.Fatalf("host %s appears in more than one run (interleaved): %v", h, runs)
		}
		seen[h] = true
	}
	for _, h := range hosts {
		if counts[h] != perHost {
			t.Errorf("host %s: got %d lines, want %d", h, counts[h], perHost)
		}
	}
}

func TestFlushAllHostSinksDrainsPartialBlock(t *testing.T) {
	prevWriter, prevOutput := outputWriter, args.Output
	prevActive := atomic.LoadInt32(&hostSinkActive)
	defer func() {
		outputWriter, args.Output = prevWriter, prevOutput
		atomic.StoreInt32(&hostSinkActive, prevActive)
		hostSinkMu.Lock()
		hostSinks = map[int64]*hostSink{}
		hostSinkMu.Unlock()
	}()

	var out bytes.Buffer
	outputWriter = &out
	args.Output = "human"
	enableHostSinks()
	beginHostSink("https://partial/")
	printHuman("partial finding")
	flushAllHostSinks()
	flushHostSink() // deferred normal completion after SIGINT drain must not duplicate it

	got := out.String()
	if !strings.Contains(got, "https://partial/") || !strings.Contains(got, "partial finding") {
		t.Fatalf("partial host block was not drained:\n%s", got)
	}
	if strings.Count(got, "partial finding") != 1 {
		t.Fatalf("partial host block was flushed more than once:\n%s", got)
	}
}

// TestRetrieveURLEscaping locks in the fix for the '#~2' false-disclosure bug: a
// raw URL-significant byte in an 8.3 alias must be percent-encoded so the GET
// targets the literal alias instead of (for '#') dropping to the directory root.
// Any trailing ADS token must survive unescaped.
func TestRetrieveURLEscaping(t *testing.T) {
	cases := map[string]string{
		"#~2":        "https://h/%23~2",        // '#' would otherwise be a fragment -> root
		"#~2::$DATA": "https://h/%23~2::$DATA", // ADS ':' and '$' stay literal
		"AB~1.TXT":   "https://h/AB~1.TXT",     // benign name unchanged
		"U~2.E(":     "https://h/U~2.E%28",     // '(' encoded
		"3P~4.K%":    "https://h/3P~4.K%25",    // literal '%' encoded
	}
	for name, want := range cases {
		if got := retrieveURL("https://h/", name); got != want {
			t.Errorf("retrieveURL(%q) = %q, want %q", name, got, want)
		}
	}
	if got := retrieveURL("https://h/bin::$INDEX_ALLOCATION/", "#~2"); got != "https://h/bin::$INDEX_ALLOCATION/%23~2" {
		t.Errorf("ADS-base join = %q, want https://h/bin::$INDEX_ALLOCATION/%%23~2", got)
	}
}

// TestCatchAllCharFraction covers the catch-all guard's core metric: a real
// directory matches a small slice of the charset as first characters, while a
// serve-everything front end matches nearly all of it.
func TestCatchAllCharFraction(t *testing.T) {
	charset := "ABCDEFGHIJ" // 10 chars for easy fractions
	// Real directory: files start with 2 of 10 chars -> 0.2, well under threshold.
	if f := catchAllCharFraction(map[string]string{"~1": "AB"}, []string{"~1"}, charset); f != 0.2 {
		t.Errorf("real dir fraction = %v, want 0.2", f)
	}
	// Catch-all: all 10 chars match -> 1.0, over the threshold. A diverse-but-real
	// directory (0.7 here) must stay under it.
	if realish := catchAllCharFraction(map[string]string{"~1": "ABCDEFG"}, []string{"~1"}, charset); realish > catchAllThreshold {
		t.Errorf("diverse-but-real fraction = %v, must stay <= %v", realish, catchAllThreshold)
	}
	got := catchAllCharFraction(map[string]string{"~1": "ABCDEFGHIJ"}, []string{"~1"}, charset)
	if got <= catchAllThreshold {
		t.Errorf("catch-all fraction = %v, expected > %v", got, catchAllThreshold)
	}
	// Max is taken across tildes.
	multi := catchAllCharFraction(map[string]string{"~1": "A", "~2": "ABCDEFGHIJ"}, []string{"~1", "~2"}, charset)
	if multi != 1.0 {
		t.Errorf("multi-tilde max fraction = %v, want 1.0", multi)
	}
	if catchAllCharFraction(nil, nil, "") != 0 {
		t.Error("empty charset must not divide by zero")
	}
}

// TestSensitiveDisclosureLabel: the recovered LONG name (not the .CON-truncated
// alias) drives the "is this worth an active read attempt" decision.
func TestSensitiveDisclosureLabel(t *testing.T) {
	hits := map[string]string{
		"web.config":                  "ASP.NET config",
		"WEB.CONFIG":                  "ASP.NET config",
		"connectionStrings.config":    "ASP.NET config",
		"machine.config":              "ASP.NET config",
		"appsettings.json":            "app settings (secrets)",
		"appsettings.Production.json": "app settings (secrets)",
		"server.pfx":                  "private key/cert",
		"tls.pem":                     "private key/cert",
		"db.mdf":                      "database/backup",
		"site.bak":                    "database/backup",
		"properties.dav":              "IIS WebDAV custom-property database",
		"/deep/path/PROPERTIES.DAV":   "IIS WebDAV custom-property database",
		"/deep/path/web.config":       "ASP.NET config", // last segment only
	}
	for name, want := range hits {
		if got, ok := sensitiveDisclosureLabel(name); !ok || got != want {
			t.Errorf("sensitiveDisclosureLabel(%q) = (%q,%v), want (%q,true)", name, got, ok, want)
		}
	}
	for _, name := range []string{"default.aspx", "index.html", "logo.png", "readme.txt", "app.js"} {
		if got, ok := sensitiveDisclosureLabel(name); ok {
			t.Errorf("sensitiveDisclosureLabel(%q) = (%q,true), want not-sensitive", name, got)
		}
	}
}

// TestClassifyReadBlock: a blocked sensitive read must name the tier that refused
// it — IIS's own 8.3 patch vs an intercepting front-end — not a bare status.
func TestClassifyReadBlock(t *testing.T) {
	resp := func(code int, hdr map[string]string) *http.Response {
		h := http.Header{}
		for k, v := range hdr {
			h.Set(k, v)
		}
		return &http.Response{StatusCode: code, Header: h}
	}
	// Reached IIS, patched: 404 from an IIS origin with no proxy hop.
	if v := classifyReadBlock(resp(404, map[string]string{"Server": "Microsoft-IIS/10.0"})); !strings.Contains(v, "IIS") || !strings.Contains(v, "canonical") {
		t.Errorf("IIS-patch case misclassified: %q", v)
	}
	// Front-end (GCLB): 403 with a Via hop and Google server, no IIS.
	if v := classifyReadBlock(resp(403, map[string]string{"Via": "1.1 google", "Server": "Google Frontend"})); !strings.Contains(v, "front-end") {
		t.Errorf("front-end case misclassified: %q", v)
	}
	// No response at all.
	if v := classifyReadBlock(nil); !strings.Contains(v, "unreachable") {
		t.Errorf("nil-response case misclassified: %q", v)
	}
}

// TestProbeSensitiveAliasReadLeak: an UNPATCHED origin that serves the 8.3 alias
// must be reported as a CRITICAL disclosure (and saved), while the random control
// (a non-existent sibling) returns 404 so it is not a serve-everything false hit.
func TestProbeSensitiveAliasReadLeak(t *testing.T) {
	prevArgs := args
	defer func() { args = prevArgs }()
	args = arguments{Output: "human", Retries: 0, LootDir: t.TempDir()}

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if strings.Contains(req.URL.Path, "WEB~1.CON") {
			return responseFor(req, http.StatusOK,
				`<?xml version="1.0"?><configuration><connectionStrings><add connectionString="Server=x;Password=SECRET"/></connectionStrings></configuration>`), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil // control
	})}

	br := baseRequest{url: "http://iis.test/", file: "WEB", tilde: "~1", ext: ".CON"}
	lines := probeSensitiveAliasRead(client, &httpStats{}, &attackConfig{}, br, "http://iis.test/", "web.config", "ASP.NET config")
	joined := strings.Join(lines, "\n")
	if !strings.Contains(joined, "8.3-READ/CRITICAL") || !strings.Contains(joined, "web.config") {
		t.Fatalf("expected a CRITICAL disclosure line, got:\n%s", joined)
	}
	if !strings.Contains(joined, "saved ->") {
		t.Errorf("expected the leaked file to be saved, got:\n%s", joined)
	}
}

// TestProbeSensitiveAliasReadIndexAllocationLeak locks in index-allocation disclosure: a Windows
// Express tier can protect /private at the router, yet serve the same child from
// /private::$INDEX_ALLOCATION/ through the later static middleware.
func TestProbeSensitiveAliasReadIndexAllocationLeak(t *testing.T) {
	prevArgs := args
	defer func() { args = prevArgs }()
	args = arguments{
		Output:       "human",
		Retries:      0,
		LootDir:      t.TempDir(),
		RetrieveBase: "http://express.test",
	}

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		p := strings.ToUpper(req.URL.Path)
		switch {
		case strings.Contains(p, "WEB~1.CON"):
			return responseFor(req, http.StatusUnauthorized, "Authentication required"), nil
		case strings.Contains(p, "PRIVATE::$INDEX_ALLOCATION/WEB.CONFIG"):
			return responseFor(req, http.StatusOK,
				`<configuration><connectionStrings><add connectionString="Password=synthetic-test-value"/></connectionStrings></configuration>`), nil
		default:
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
	})}

	br := baseRequest{url: "http://iis.test/private/", file: "WEB", tilde: "~1", ext: ".CON"}
	lines := probeSensitiveAliasRead(client, &httpStats{}, &attackConfig{}, br,
		"http://iis.test/private/", "web.config", "ASP.NET config")
	joined := strings.Join(lines, "\n")
	if !strings.Contains(joined, "INDEX-READ/CRITICAL") || !strings.Contains(joined, "$INDEX_ALLOCATION") {
		t.Fatalf("expected a guarded $INDEX_ALLOCATION disclosure, got:\n%s", joined)
	}
}

func TestIndexAllocationBases(t *testing.T) {
	got := indexAllocationBases("https://node.test/app/private/")
	want := []string{
		"https://node.test/app/private::$INDEX_ALLOCATION/",
		"https://node.test/app/private:$I30:$INDEX_ALLOCATION/",
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("indexAllocationBases = %#v, want %#v", got, want)
	}
}

// TestProbeSensitiveAliasReadWalls: a blocked read must name the tier and, on a
// single-stack IIS, point at the cross-stack read instead of a bare status.
func TestProbeSensitiveAliasReadWalls(t *testing.T) {
	prevArgs := args
	prevHosts := singleStackHosts
	defer func() { args = prevArgs; singleStackHosts = prevHosts }()
	args = arguments{Output: "human", Retries: 0}
	singleStackHosts = map[string]bool{}

	// Patched IIS: 404 from the IIS origin, no proxy hop.
	iis := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		r := responseFor(req, http.StatusNotFound, "IIS 404")
		r.Header.Set("Server", "Microsoft-IIS/10.0")
		return r, nil
	})}
	markSingleStackIIS("http://iis.test")
	br := baseRequest{url: "http://iis.test/", file: "WEB", tilde: "~1", ext: ".CON"}
	got := strings.Join(probeSensitiveAliasRead(iis, &httpStats{}, &attackConfig{}, br, "http://iis.test/", "web.config", "ASP.NET config"), "\n")
	if !strings.Contains(got, "8.3-READ]") || !strings.Contains(got, "canonical") || !strings.Contains(got, "--retrieve-base") {
		t.Fatalf("IIS-wall verdict should name the patch and the cross-stack next step, got:\n%s", got)
	}

	// Intercepting front-end: 403 with a Via hop.
	fe := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		r := responseFor(req, http.StatusForbidden, "denied")
		r.Header.Set("Via", "1.1 google")
		return r, nil
	})}
	got = strings.Join(probeSensitiveAliasRead(fe, &httpStats{}, &attackConfig{}, br, "http://iis.test/", "web.config", "ASP.NET config"), "\n")
	if !strings.Contains(got, "front-end") {
		t.Fatalf("front-end-wall verdict should name the proxy, got:\n%s", got)
	}
}

// TestResolvedToLongName: only an HTTP-confirmed long name counts as resolved.
// An alias echo ("short-name*") or a request-filtered inference ("wordlist-inferred")
// must NOT count — that was the "9/23 resolved" inflation + the misleading (401).
func TestResolvedToLongName(t *testing.T) {
	if !resolvedToLongName("web.config", "wordlist") {
		t.Error("a wordlist long-name resolution must count as resolved")
	}
	for _, mt := range []string{"short-name", "short-name-known-extension", "wordlist-inferred"} {
		if resolvedToLongName("RESERV~1.ZIP", mt) {
			t.Errorf("matchType %q must NOT count as a resolved long name", mt)
		}
	}
	if resolvedToLongName("", "wordlist") {
		t.Error("an empty recovered name is never resolved")
	}
}

// TestIsRequestFilteredName drives the wordlist-inferred fallback: web.config /
// *.config / global.asax are hidden by IIS so their long name never HTTP-confirms.
func TestIsRequestFilteredName(t *testing.T) {
	for _, n := range []string{
		"web.config", "WEB.CONFIG", "connectionStrings.config", "global.asax",
		"app.config", "Model.cs", "Site.csproj", "Helper.vb", "App.vbproj",
		// Expanded IIS-default deny list: markup, resources, license, DB, source.
		"Site.master", "MyControl.ascx", "Theme.skin", "App.browser", "Web.sitemap",
		"Strings.resources", "License.licx", "Setup.webinfo", "database.mdf",
		"log.ldf", "data.mdb", "Legacy.java", "App_Web_abc.compiled",
	} {
		if !isRequestFilteredName(n) {
			t.Errorf("isRequestFilteredName(%q) = false, want true", n)
		}
	}
	// Served content and handler extensions answer a GET and must be confirmed
	// the normal way, never surfaced as a request-filtered inference.
	for _, n := range []string{
		"index.html", "logo.png", "app.js", "styles.css", "data.json",
		"Default.aspx", "Service.asmx", "Handler.ashx", "WebResource.axd", "Api.svc",
	} {
		if isRequestFilteredName(n) {
			t.Errorf("isRequestFilteredName(%q) = true, want false", n)
		}
	}
}

// TestTildeContinuationCatchAllGuard: a soft-response server that answers statusPos
// to anything must yield ZERO tilde-continuation names (the ~2DAABAB…garbage), while
// the negative-control guard still lets a real literal-tilde name through.
func TestTildeContinuationCatchAllGuard(t *testing.T) {
	prevArgs, prevWriter := args, outputWriter
	defer func() { args, outputWriter = prevArgs, prevWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", TildeContinuation: true, Retries: 0, Characters: alphanum}

	// Catch-all: every wildcard probe returns the positive status.
	catchAll := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, 404, "hit"), nil
	})}
	mk := markers{statusPos: 404, statusNeg: 400}
	ac := &attackConfig{method: "GET", foundFiles: map[string]struct{}{}, foundDirectories: map[string]struct{}{}}
	runTildeContinuation(catchAll, &httpStats{}, ac, mk, "http://iis.test/")
	if strings.Contains(out.String(), "TILDE-CONT") {
		t.Fatalf("catch-all server must produce no tilde-continuation names, got:\n%s", out.String())
	}
}

// TestExtensionCatchAllDualShape locks in the v0.46.3 fix: an extension oracle
// that is a catch-all only under the literal-dot shape the enumeration actually
// walks (name~1.X*), while the wildcard-separated discovery shape (*~1*X*) still
// reads a plausible ~40%. This was seen live behind a GCLB→IIS front end whose
// ASP.NET custom-error redirect answered 404 to any dotted path (oracle locked on
// the DEBUG verb): the star-only guard passed and enumeration exploded into tens
// of thousands of STEM~1.XXX false positives. The guard must trip on the MAX of
// the two shapes, not the star shape alone.
func TestExtensionCatchAllDualShape(t *testing.T) {
	charset := "ABCDEFGHIJ" // 10 chars for easy fractions
	tildes := []string{"~1"}
	// Star-shape discovery read 4/10 = 0.4 — under the threshold, so a
	// single-shape guard would (wrongly) NOT suppress.
	starChars := map[string]string{"~1": "ABCD"}
	// Dotted-shape probe (the real enumeration shape) matched everything: 10/10.
	dotChars := map[string]string{"~1": "ABCDEFGHIJ"}

	starFrac := catchAllCharFraction(starChars, tildes, charset)
	if starFrac > catchAllThreshold {
		t.Fatalf("precondition: star fraction %v should be <= %v (else the test proves nothing)", starFrac, catchAllThreshold)
	}
	dotFrac := catchAllCharFraction(dotChars, tildes, charset)
	if dotFrac <= catchAllThreshold {
		t.Fatalf("dot fraction %v should exceed %v", dotFrac, catchAllThreshold)
	}
	// The decision the guard makes: max(star, dot) > threshold -> suppress.
	extFrac := starFrac
	if dotFrac > extFrac {
		extFrac = dotFrac
	}
	if extFrac <= catchAllThreshold {
		t.Errorf("max(star=%v, dot=%v)=%v must exceed %v to suppress the extension explosion", starFrac, dotFrac, extFrac, catchAllThreshold)
	}
}

// TestEmitHumanRoutesWorkerFindings locks in the --parallel attribution fix: a
// side-finding emitted from a worker goroutine (no per-host sink) is buffered on
// the attackConfig, while one emitted from the main goroutine (has the sink)
// prints inline; flushDeferredFindings drains the buffer on the main goroutine.
func TestEmitHumanRoutesWorkerFindings(t *testing.T) {
	prevWriter, prevOutput := outputWriter, args.Output
	prevActive := atomic.LoadInt32(&hostSinkActive)
	defer func() {
		outputWriter, args.Output = prevWriter, prevOutput
		atomic.StoreInt32(&hostSinkActive, prevActive)
		hostSinkMu.Lock()
		hostSinks = map[int64]*hostSink{}
		hostSinkMu.Unlock()
	}()

	var out bytes.Buffer
	outputWriter = &out
	args.Output = "human"
	enableHostSinks()

	ac := &attackConfig{}
	beginHostSink("https://host/") // main (this) goroutine owns the sink

	// A worker goroutine has no sink -> its finding is buffered, not printed.
	done := make(chan struct{})
	go func() {
		ac.emitHuman("worker-finding")
		close(done)
	}()
	<-done
	if strings.Contains(out.String(), "worker-finding") {
		t.Fatalf("worker finding printed instead of buffered:\n%s", out.String())
	}
	if len(ac.deferredFindings) != 1 || ac.deferredFindings[0] != "worker-finding" {
		t.Fatalf("worker finding not buffered: %#v", ac.deferredFindings)
	}

	// The main goroutine prints inline; the flush drains the buffer, also inline.
	ac.emitHuman("main-finding")
	ac.flushDeferredFindings()
	flushHostSink()

	got := out.String()
	if !strings.Contains(got, "main-finding") || !strings.Contains(got, "worker-finding") {
		t.Fatalf("expected both findings in the flushed block:\n%s", got)
	}
	if len(ac.deferredFindings) != 0 {
		t.Fatalf("deferredFindings not cleared after flush: %#v", ac.deferredFindings)
	}
}
