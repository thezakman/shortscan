package shortscan

import (
	"net/http"
	"regexp"
	"strings"
	"testing"
)

// noHTTPTransport fails the test if a request is ever made — used to prove a
// code path returns before touching the network.
type noHTTPTransport struct{ t *testing.T }

func (n noHTTPTransport) RoundTrip(req *http.Request) (*http.Response, error) {
	n.t.Fatalf("unexpected HTTP request: %s", req.URL.String())
	return nil, nil
}

func TestRecordTildeContinuationFindingWithoutRecurse(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0, Recurse: false}

	client := &http.Client{Transport: noHTTPTransport{t}}
	ac := &attackConfig{foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{})}
	recordTildeContinuationFinding(client, &httpStats{}, ac, "https://example.test/", "Report~2final.docx", false)

	if _, ok := ac.foundFiles["report~2final.docx"]; !ok {
		t.Fatal("recovered name was not recorded in foundFiles")
	}
	if len(ac.foundDirectories) != 0 {
		t.Fatalf("directory recursion should not run without --recurse: %#v", ac.foundDirectories)
	}
}

func TestRecordTildeContinuationFindingExtensionlessQueuesRecursion(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0, Recurse: true}

	client := &http.Client{Transport: noHTTPTransport{t}}
	ac := &attackConfig{foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{})}
	recordTildeContinuationFinding(client, &httpStats{}, ac, "https://example.test/", "Backup~2024", true)

	if _, ok := ac.foundDirectories["Backup~2024"]; !ok {
		t.Fatal("extensionless recovered name was not queued for recursive validation")
	}
}

func TestRecordTildeContinuationFindingWithExtensionNeedsRedirect(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0, Recurse: true}

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusOK, "ordinary file"), nil
	})}
	ac := &attackConfig{foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{})}
	recordTildeContinuationFinding(client, &httpStats{}, ac, "https://example.test/", "db~1.bak", false)

	if len(ac.foundDirectories) != 0 {
		t.Fatalf("ordinary file was queued as a directory: %#v", ac.foundDirectories)
	}
}

func TestRecordTildeContinuationFindingWithExtensionRedirectsToDirectory(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0, Recurse: true}

	client := &http.Client{
		Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
			res := responseFor(req, http.StatusMovedPermanently, "")
			res.Header.Set("Location", "/Report~2final.dir/")
			return res, nil
		}),
		// Production's client (transport.go) disables auto-follow so a bare 301
		// can be inspected for a directory redirect; mirror that here, or the
		// default client chases the Location header until "stopped after 10
		// redirects" and fetch() returns an error instead of the 301.
		CheckRedirect: func(req *http.Request, via []*http.Request) error { return http.ErrUseLastResponse },
	}
	ac := &attackConfig{foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{})}
	recordTildeContinuationFinding(client, &httpStats{}, ac, "https://example.test/", "Report~2final.dir", false)

	if _, ok := ac.foundDirectories["Report~2final.dir"]; !ok {
		t.Fatal("directory-redirecting recovered name was not queued for recursion")
	}
}

func TestRecordTildeContinuationFindingSeedsReferenceCrawl(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0, Recurse: false, CrawlReferences: true}

	client := &http.Client{Transport: noHTTPTransport{t}}
	ac := &attackConfig{foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{})}
	recordTildeContinuationFinding(client, &httpStats{}, ac, "https://example.test/", "report~1final.html", false)

	if _, ok := ac.referenceSeeds["https://example.test/report~1final.html"]; !ok {
		t.Fatalf("crawlable recovered name did not seed the reference crawler: %#v", ac.referenceSeeds)
	}
}

// TestTildeContinuationRecoversFullNameUnderConcurrency proves the batched
// concurrent char-by-char walk (firstChar in runTildeContinuation) still
// recovers the exact right name, one character at a time, in prefix/suffix/ext
// order, when args.Concurrency makes each alphabet batch run several probes at
// once instead of one at a time — the happy path had no direct test before the
// walk was parallelized.
func TestTildeContinuationRecoversFullNameUnderConcurrency(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Output: "ndjson", TildeContinuation: true, Retries: 0, Concurrency: 6}

	const realName = "REPORT~2FINAL.DOCX"
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		pattern := strings.ToUpper(strings.TrimPrefix(req.URL.Path, "/"))
		re := regexp.MustCompile("^" + strings.ReplaceAll(regexp.QuoteMeta(pattern), `\*`, ".*") + "$")
		if re.MatchString(realName) {
			return responseFor(req, 200, "hit"), nil
		}
		return responseFor(req, 404, "missing"), nil
	})}
	mk := markers{statusPos: 200, statusNeg: 404}
	ac := &attackConfig{method: "GET", foundFiles: map[string]struct{}{}, foundDirectories: map[string]struct{}{}}
	runTildeContinuation(client, &httpStats{}, ac, mk, "http://iis.test/")

	if _, ok := ac.foundFiles["report~2final.docx"]; !ok {
		t.Fatalf("expected %q recovered into foundFiles, got %#v", realName, ac.foundFiles)
	}
}

// TestTildeContinuationSkipsKnownAlias locks in the dedup that keeps the
// [TILDE-CONT] section from echoing an 8.3 alias the classic scan already reported
// (e.g. WEB~1.CON, whose base is < 6 so the fixed-6 degenerate guard never catches
// it). The same oracle recovers the name; the only difference is whether the alias
// is already in ac.enumEntries.
func TestTildeContinuationSkipsKnownAlias(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Output: "ndjson", TildeContinuation: true, Retries: 0, Concurrency: 6}

	const alias = "WEB~1.CON" // web.config's generated 8.3 short name
	newClient := func() *http.Client {
		return &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
			pattern := strings.ToUpper(strings.TrimPrefix(req.URL.Path, "/"))
			re := regexp.MustCompile("^" + strings.ReplaceAll(regexp.QuoteMeta(pattern), `\*`, ".*") + "$")
			if re.MatchString(alias) {
				return responseFor(req, 200, "hit"), nil
			}
			return responseFor(req, 404, "missing"), nil
		})}
	}
	mk := markers{statusPos: 200, statusNeg: 404}

	// Control: with no known alias, the walk recovers WEB~1.CON as usual.
	ctrl := &attackConfig{method: "GET", foundFiles: map[string]struct{}{}, foundDirectories: map[string]struct{}{}}
	runTildeContinuation(newClient(), &httpStats{}, ctrl, mk, "http://iis.test/")
	if _, ok := ctrl.foundFiles["web~1.con"]; !ok {
		t.Fatalf("control: expected %q recovered when not already a known alias, got %#v", alias, ctrl.foundFiles)
	}

	// With the alias already buffered by the classic scan, it must be dropped.
	ac := &attackConfig{method: "GET", foundFiles: map[string]struct{}{}, foundDirectories: map[string]struct{}{}}
	bufferEnum(ac, alias, "", alias, false)
	runTildeContinuation(newClient(), &httpStats{}, ac, mk, "http://iis.test/")
	if _, ok := ac.foundFiles["web~1.con"]; ok {
		t.Fatalf("expected known alias %q to be skipped by [TILDE-CONT], but it was recovered", alias)
	}
}

func TestTildeContinuationDoesNotTrustTentativeAlias(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Output: "ndjson", TildeContinuation: true, Retries: 0, Concurrency: 6}

	const alias = "AB~1.TXT"
	hc := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		pattern := strings.ToUpper(strings.TrimPrefix(req.URL.Path, "/"))
		re := regexp.MustCompile("^" + strings.ReplaceAll(regexp.QuoteMeta(pattern), `\*`, ".*") + "$")
		if re.MatchString(alias) {
			return responseFor(req, 200, "hit"), nil
		}
		return responseFor(req, 404, "missing"), nil
	})}
	ac := &attackConfig{method: "GET", foundFiles: map[string]struct{}{}, foundDirectories: map[string]struct{}{}}
	bufferTentativeEnum(ac, alias, alias+" [tentative]")
	runTildeContinuation(hc, &httpStats{}, ac, markers{statusPos: 200, statusNeg: 404}, "http://iis.test/")
	if _, ok := ac.foundFiles[strings.ToLower(alias)]; !ok {
		t.Fatalf("tentative alias %q suppressed a stronger tilde-continuation recovery", alias)
	}
}
