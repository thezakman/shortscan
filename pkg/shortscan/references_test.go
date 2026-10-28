package shortscan

import (
	"bytes"
	"net/http"
	"regexp"
	"strings"
	"sync"
	"testing"
)

func TestExtractReferenceValuesFindsHTMLCSSAndJavaScriptPaths(t *testing.T) {
	body := []byte(`
		<a href="/sis_erp/sis.login.aspx">login</a>
		<script src='/sis_erp/sis/login.js'></script>
		<style>body { background: url("../images/bg.png") }</style>
		<script>window.location = 'sis.seguranca.wprecuperasenha.aspx';</script>
	`)
	got := make(map[string]struct{})
	for _, value := range extractReferenceValues(body) {
		got[value] = struct{}{}
	}
	for _, want := range []string{
		"/sis_erp/sis.login.aspx",
		"/sis_erp/sis/login.js",
		"../images/bg.png",
		"sis.seguranca.wprecuperasenha.aspx",
	} {
		if _, exists := got[want]; !exists {
			t.Errorf("reference %q missing from %#v", want, got)
		}
	}
}

func TestExtractReferenceValuesKeepsModernAndCompressedAssetNames(t *testing.T) {
	body := []byte(`"worker.wasm" "site.webmanifest" "font.woff2" "service-worker.js.br" "bundle.js.gz"`)
	got := make(map[string]struct{})
	for _, value := range extractReferenceValues(body) {
		got[value] = struct{}{}
	}
	for _, want := range []string{"worker.wasm", "site.webmanifest", "font.woff2", "service-worker.js.br", "bundle.js.gz"} {
		if _, exists := got[want]; !exists {
			t.Errorf("reference %q missing from %#v", want, got)
		}
	}
}

func TestReferenceChecksumCandidateMapsHashedAliasWithoutRainbow(t *testing.T) {
	previousArgs, previousRegex := args, checksumRegex
	t.Cleanup(func() {
		args, checksumRegex = previousArgs, previousRegex
	})
	args = arguments{CrawlReferences: true}
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")

	knowledge := newReferenceKnowledge()
	knowledge.rememberURL("http://example.test/PRIMAX5145", "http://example.test/app.js")
	ac := &attackConfig{references: knowledge}
	br := baseRequest{url: "http://example.test/", file: "PR45F4", tilde: "~1"}

	candidates := referenceFilenameCandidates(ac, br)
	if len(candidates) != 1 {
		t.Fatalf("reference checksum candidates = %+v, want one", candidates)
	}
	if candidates[0].matchType != "reference-checksum" ||
		candidates[0].record.filename != "PRIMAX5145" {
		t.Fatalf("unexpected checksum candidate: %+v", candidates[0])
	}

	br.file = "PRFFFF"
	if candidates := referenceFilenameCandidates(ac, br); len(candidates) != 0 {
		t.Fatalf("wrong checksum produced candidates: %+v", candidates)
	}
	br.url = "http://other.example/"
	br.file = "PR45F4"
	if candidates := referenceFilenameCandidates(ac, br); len(candidates) != 0 {
		t.Fatalf("reference checksum knowledge leaked across origins: %+v", candidates)
	}
}

func TestReferenceCompressedCompanionMapsJavaScriptToBrotliAlias(t *testing.T) {
	previousArgs, previousRegex := args, checksumRegex
	t.Cleanup(func() {
		args, checksumRegex = previousArgs, previousRegex
	})
	args = arguments{CrawlReferences: true}
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")

	knowledge := newReferenceKnowledge()
	knowledge.rememberURL("http://example.test/service-worker.js", "http://example.test/index.html")
	ac := &attackConfig{references: knowledge}
	br := baseRequest{url: "http://example.test/", file: "SERVIC", tilde: "~1", ext: ".BR"}

	candidates := referenceFilenameCandidates(ac, br)
	found := false
	for _, candidate := range candidates {
		if candidate.record.filename+candidate.record.extension == "service-worker.js.br" &&
			candidate.matchType == "reference-compressed" {
			found = true
		}
	}
	if !found {
		t.Fatalf("compressed reference candidate missing: %+v", candidates)
	}

	companion, ok := compressedCompanionRecord(knowledge.recordsFor(br.url)[0].record, "BR")
	if !ok || len(companion.checksums) < 4 {
		t.Fatalf("compressed companion checksum missing: %+v", companion)
	}
	br.file = "SE" + companion.checksums[:4]
	candidates = referenceFilenameCandidates(ac, br)
	found = false
	for _, candidate := range candidates {
		if candidate.record.filename+candidate.record.extension == "service-worker.js.br" &&
			candidate.matchType == "reference-compressed-checksum" {
			found = true
		}
	}
	if !found {
		t.Fatalf("checksummed compressed reference candidate missing: %+v", candidates)
	}

	br.ext = ".ZIP"
	if candidates := referenceFilenameCandidates(ac, br); len(candidates) != 0 {
		t.Fatalf("non-compression extension derived companions: %+v", candidates)
	}
}

func TestReferenceCrawlerBuildsTargetSpecificCandidates(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{CrawlReferences: true, Retries: 0}

	var mutex sync.Mutex
	requests := make(map[string]int)
	baseURL := "http://reference.test"
	client := &http.Client{Transport: roundTripFunc(func(r *http.Request) (*http.Response, error) {
		mutex.Lock()
		requests[r.URL.Path]++
		mutex.Unlock()
		var response *http.Response
		switch r.URL.Path {
		case "/sis_erp/sis.login.aspx":
			response = responseFor(r, http.StatusOK, `<script src="sis/login.js"></script><script src="https://external.invalid/skip.js"></script>`)
			response.Header.Set("Content-Type", "text/html; charset=utf-8")
		case "/sis_erp/sis/login.js":
			response = responseFor(r, http.StatusOK, `window.location = 'sis.seguranca.wprecuperasenha.aspx';`)
			response.Header.Set("Content-Type", "application/javascript")
		default:
			response = responseFor(r, http.StatusNotFound, "missing")
		}
		return response, nil
	})}

	knowledge := newReferenceKnowledge()
	crawler := newReferenceCrawler(knowledge, 8, 2, 8192)
	stats := crawler.crawl(client, &httpStats{}, baseURL+"/", []string{"/sis_erp/sis.login.aspx"})
	if stats.pages != 3 || stats.errors != 0 {
		t.Fatalf("crawl stats = %+v, want HTML, JS and one referenced endpoint", stats)
	}
	mutex.Lock()
	if requests["/sis_erp/sis.login.aspx"] != 1 || requests["/sis_erp/sis/login.js"] != 1 ||
		requests["/sis_erp/sis/sis.seguranca.wprecuperasenha.aspx"] != 1 || len(requests) != 3 {
		t.Fatalf("unexpected bounded crawl requests: %#v", requests)
	}
	mutex.Unlock()

	records := knowledge.recordsFor(baseURL + "/")
	names := make(map[string]referenceEvidence)
	for _, evidence := range records {
		names[evidence.record.filename+evidence.record.extension] = evidence
	}
	for _, want := range []string{"sis_erp", "sis.login.aspx", "sis", "login.js", "sis.seguranca.wprecuperasenha.aspx"} {
		if _, exists := names[want]; !exists {
			t.Errorf("target-derived name %q missing from %+v", want, names)
		}
	}

	evidence := names["sis.seguranca.wprecuperasenha.aspx"]
	br := baseRequest{
		url: baseURL + "/sis_erp/sis/", file: evidence.record.filename83,
		tilde: "~1", ext: "." + evidence.record.extension83,
	}
	ac := &attackConfig{references: knowledge}
	candidates := referenceFilenameCandidates(ac, br)
	if len(candidates) != 1 || candidates[0].matchType != "reference" ||
		candidates[0].record.filename+candidates[0].record.extension != "sis.seguranca.wprecuperasenha.aspx" {
		t.Fatalf("reference candidates = %+v", candidates)
	}
	br.url = "http://other.example/sis_erp/sis/"
	if candidates := referenceFilenameCandidates(ac, br); len(candidates) != 0 {
		t.Fatalf("reference knowledge leaked across origins: %+v", candidates)
	}
}

func TestReferenceCrawlerHonoursPageBudget(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{CrawlReferences: true, Retries: 0}

	requests := 0
	baseURL := "http://budget.test"
	client := &http.Client{Transport: roundTripFunc(func(r *http.Request) (*http.Response, error) {
		requests++
		response := responseFor(r, http.StatusOK, `<a href="/next.html">next</a>`)
		response.Header.Set("Content-Type", "text/html")
		return response, nil
	})}
	crawler := newReferenceCrawler(newReferenceKnowledge(), 1, 4, 4096)
	stats := crawler.crawl(client, &httpStats{}, baseURL+"/", []string{baseURL + "/start.html"})
	if stats.pages != 1 || requests != 1 {
		t.Fatalf("page budget was not enforced: stats=%+v requests=%d", stats, requests)
	}
}

func TestReferenceOnlySkipsConfiguredWordlist(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{Autocomplete: "method", ReferenceOnly: true}
	if needsConfiguredWordlist(args.Autocomplete) {
		t.Fatal("reference-only unexpectedly requested wordlist loading")
	}
	args.ReferenceOnly = false
	if !needsConfiguredWordlist(args.Autocomplete) {
		t.Fatal("normal autocomplete should request wordlist loading")
	}
}

func TestReferenceRecoveryRetriesAliasAfterCrawl(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache := statusCache
	t.Cleanup(func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache = previousStatusCache
	})
	args = arguments{
		CrawlReferences: true, Autocomplete: "method", Output: "human",
		Retries: 0,
	}
	var output bytes.Buffer
	outputWriter = &output
	// The "method" oracle's 405 baseline validation reads/writes the package-level
	// statusCache — must be initialized here, not left to an earlier test's leftover state.
	statusCache = make(map[string]map[int]struct{})
	knowledge := newReferenceKnowledge()
	knowledge.rememberURL("http://example.test/COMERCIAL.ASPX", "http://example.test/index.html")
	ac := &attackConfig{
		autocomplete:     args.Autocomplete,
		references:       knowledge,
		foundFiles:       make(map[string]struct{}),
		foundDirectories: make(map[string]struct{}),
	}
	observeRecoveryAlias(ac, baseRequest{
		url: "http://example.test/", file: "COMERC", tilde: "~1", ext: ".ASP",
	})

	requests, aliasProbes := 0, 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests++
		if req.Method == "_" && req.URL.Path == "/COMERCIAL.ASPX" {
			aliasProbes++
			return responseFor(req, http.StatusMethodNotAllowed, "confirmed page"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	if recovered := recoverReferenceAliases(client, &httpStats{}, ac, nil); recovered != 1 {
		t.Fatalf("recovered %d reference paths, want 1", recovered)
	}
	if _, exists := ac.foundFiles["comercial.aspx"]; !exists {
		t.Fatalf("confirmed reference path was not recorded: %#v", ac.foundFiles)
	}
	// The alias is confirmed with a single method probe; method-magic then validates
	// that 405 against a per-extension baseline (random same-extension misses, which
	// hit other paths), so the alias itself must not be re-probed.
	if aliasProbes != 1 {
		t.Fatalf("reference recovery probed the alias %d times, want exactly 1 (of %d total)", aliasProbes, requests)
	}
	seeds := takeReferenceSeeds(ac)
	if len(seeds) != 1 || seeds[0] != "http://example.test/COMERCIAL.ASPX" {
		t.Fatalf("confirmed page was not queued as a reference seed: %#v", seeds)
	}
	for _, want := range []string{"[REF-RECOVER]", "status 405", "COMERC~*.ASP", "COMERCIAL.ASPX", "reference from", "ordinal unverified"} {
		if !strings.Contains(output.String(), want) {
			t.Errorf("output omitted %q: %q", want, output.String())
		}
	}
}
