package shortscan

import (
	"bytes"
	"io"
	"net/http"
	"regexp"
	"strings"
	"sync"
	"testing"
	"time"
)

type roundTripFunc func(*http.Request) (*http.Response, error)

func (f roundTripFunc) RoundTrip(req *http.Request) (*http.Response, error) {
	return f(req)
}

type trackingBody struct {
	reads  *int
	closes *int
}

func (b trackingBody) Read([]byte) (int, error) {
	(*b.reads)++
	return 0, io.EOF
}

func (b trackingBody) Close() error {
	(*b.closes)++
	return nil
}

func responseFor(req *http.Request, status int, body string) *http.Response {
	return &http.Response{
		StatusCode: status,
		Status:     http.StatusText(status),
		Header:     make(http.Header),
		Body:       io.NopCloser(strings.NewReader(body)),
		Request:    req,
	}
}

// newWordlistConfig builds a wordlistConfig directly from sources. Production uses
// configureWordlists (path-based); the tests need to inject in-memory sources, so
// this constructor lives with the test helpers.
func newWordlistConfig(sources []wordlistSource) *wordlistConfig {
	return &wordlistConfig{sources: sources, loadDone: make(chan struct{})}
}

func TestSessionToken(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	cases := map[string]string{
		"d":     "(S(d))",
		"x":     "(S(x))",
		"f":     "(F(x))",
		"a":     "(A(x))",
		"empty": "(S())",
	}
	for style, want := range cases {
		args.SessionStyle = style
		if got := sessionToken(); got != want {
			t.Errorf("style %q: got %q want %q", style, got, want)
		}
	}
}

func TestReplaceBinAllocationEmptySession(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args.SessionStyle = "empty"
	args.SessionEncoding = "literal"
	out := replaceBinALLOCATION("https://example.invalid/bin::$INDEX_ALLOCATION")
	if want := "https://example.invalid/(S())/b/(S())in/"; out != want {
		t.Fatalf("got %q want %q", out, want)
	}
}

func TestSessionPathTokens(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args.SessionStyle = "empty"

	cases := map[string][2]string{
		"literal":         {"(S())", "(S())"},
		"outer":           {"%28S()%29", "%28S()%29"},
		"asymmetric":      {"%28S()%29", "%28S%28%29%29"},
		"asymmetric-full": {"%28S()%29", "%28%53%28%29%29"},
	}
	for encoding, want := range cases {
		args.SessionEncoding = encoding
		first, second := sessionPathTokens()
		if first != want[0] || second != want[1] {
			t.Errorf("encoding %q: got (%q, %q) want (%q, %q)", encoding, first, second, want[0], want[1])
		}
	}
}

func TestReplaceBinAllocationSessionEncoding(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args.SessionStyle = "d"

	cases := map[string]string{
		"literal":         "https://example.invalid/(S(d))/b/(S(d))in/",
		"outer":           "https://example.invalid/%28S(d)%29/b/%28S(d)%29in/",
		"asymmetric":      "https://example.invalid/%28S(d)%29/b/%28S%28d%29%29in/",
		"asymmetric-full": "https://example.invalid/%28S(d)%29/b/%28%53%28%64%29%29in/",
	}
	for encoding, want := range cases {
		args.SessionEncoding = encoding
		if got := replaceBinALLOCATION("https://example.invalid/bin::$INDEX_ALLOCATION"); got != want {
			t.Errorf("encoding %q: got %q want %q", encoding, got, want)
		}
	}
}

func TestNewHTTPRequestPreservesAsymmetricSessionEncoding(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args.SessionStyle = "d"
	args.SessionEncoding = "asymmetric"

	rawURL := replaceBinALLOCATION("https://example.invalid/bin::$INDEX_ALLOCATION")
	req, err := newHTTPRequest(http.MethodGet, rawURL, nil)
	if err != nil {
		t.Fatal(err)
	}
	wantPath := "/%28S(d)%29/b/%28S%28d%29%29in/"
	if got := req.URL.EscapedPath(); got != wantPath {
		t.Fatalf("escaped path got %q want %q", got, wantPath)
	}
	if got := req.URL.RequestURI(); got != wantPath {
		t.Fatalf("request URI got %q want %q", got, wantPath)
	}
}

func TestNewHTTPRequestPreservesFullyEncodedSecondSessionToken(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args.SessionStyle = "d"
	args.SessionEncoding = "asymmetric-full"

	rawURL := replaceBinALLOCATION("https://example.invalid/bin::$INDEX_ALLOCATION")
	req, err := newHTTPRequest(http.MethodGet, rawURL, nil)
	if err != nil {
		t.Fatal(err)
	}
	wantPath := "/%28S(d)%29/b/%28%53%28%64%29%29in/"
	if got := req.URL.EscapedPath(); got != wantPath {
		t.Fatalf("escaped path got %q want %q", got, wantPath)
	}
	if got := req.URL.RequestURI(); got != wantPath {
		t.Fatalf("request URI got %q want %q", got, wantPath)
	}
}

func TestEncodeTilde(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	cases := map[string]string{
		"default":     "~",
		"percent":     "%7E",
		"unicode":     "%EF%BD%9E",
		"double":      "%257E",
		"iis-unicode": "%u007e",
	}
	for mode, want := range cases {
		args.TildeEncoding = mode
		if got := encodeTilde(); got != want {
			t.Errorf("mode %q: got %q want %q", mode, got, want)
		}
	}
}

func TestTildify(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args.TildeEncoding = "default"
	if got := tildify("~1"); got != "~1" {
		t.Errorf("default: got %q", got)
	}
	args.TildeEncoding = "double"
	if got := tildify("~1"); got != "%257E1" {
		t.Errorf("double: got %q", got)
	}
}

func TestReplaceBinALLOCATIONCaseInsensitive(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args.SessionStyle = "d"
	args.SessionEncoding = "literal"
	for _, in := range []string{
		"https://h/foo/bin::$INDEX_ALLOCATION",
		"https://h/foo/BIN::$INDEX_ALLOCATION",
		"https://h/foo/Bin::$Index_Allocation",
	} {
		out := replaceBinALLOCATION(in)
		if !strings.Contains(out, "(S(d))/b/(S(d))in/") {
			t.Errorf("input %q produced %q (no S(d) substitution)", in, out)
		}
		if strings.Contains(out, "::$INDEX_ALLOCATION") || strings.Contains(out, "::$Index_Allocation") {
			t.Errorf("input %q not fully rewritten: %q", in, out)
		}
	}
}

func TestInspectDisclosure(t *testing.T) {
	tests := map[string][]byte{
		"MZ binary (.dll/.exe)":          {0x4D, 0x5A, 0x90, 0x00},
		"ZIP/PK archive":                 {0x50, 0x4B, 0x03, 0x04, 0x00},
		"ASP/ASP.NET source":             []byte("<%@ Page Language=\"C#\" %>"),
		"C# source":                      []byte("using System;\nnamespace Foo {}"),
		"web.config / connection string": []byte("<configuration><connectionString>..."),
		"PEM key/certificate":            []byte("-----BEGIN RSA PRIVATE KEY-----"),
		"IIS WebDAV property store (properties.dav)": append([]byte{0xff, 0xfe}, func() []byte {
			s := "\r\n[/CustomerContractDocument.txt]\r\n0063006C006100730073=1SYNTHETIC%2DSECRET!0!0\r\n"
			out := make([]byte, 0, len(s)*2)
			for _, r := range s {
				out = append(out, byte(r), byte(r>>8))
			}
			return out
		}()...),
	}
	for want, body := range tests {
		got, dt := inspectDisclosure(body)
		if !got || dt != want {
			t.Errorf("body %q: disclosed=%v type=%q (want %q)", body[:min(20, len(body))], got, dt, want)
		}
	}
	if got, _ := inspectDisclosure([]byte("hello world")); got {
		t.Error("benign body falsely flagged")
	}
}

func TestPathEscape(t *testing.T) {
	if got := pathEscape("hello world"); got != "hello%20world" {
		t.Errorf("got %q", got)
	}
	if got := pathEscape("a+b"); got != "a%2Bb" {
		t.Errorf("plus encoding: got %q", got)
	}
}

func TestRedirectsToDirectoryNormalizesLocation(t *testing.T) {
	request, err := http.NewRequest("HEAD", "https://example.test/base/Salesforce", nil)
	if err != nil {
		t.Fatal(err)
	}
	for _, location := range []string{
		"Salesforce/?from=proxy",
		"/base/Salesforce/?from=proxy",
		"https://example.test/base/Salesforce/?from=proxy",
	} {
		res := responseFor(request, http.StatusMovedPermanently, "")
		res.Header.Set("Location", location)
		if !redirectsToDirectory(res, request.URL.String()) {
			t.Errorf("directory redirect %q was not recognized", location)
		}
	}

	res := responseFor(request, http.StatusFound, "")
	res.Header.Set("Location", "/login")
	if redirectsToDirectory(res, request.URL.String()) {
		t.Fatal("unrelated redirect was classified as a directory redirect")
	}
}

func TestMarkResolvedExtensionlessPathQueuesRecursiveValidation(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0, Recurse: true}

	ac := &attackConfig{foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{})}
	markResolvedFile(ac, baseRequest{
		url: "https://example.test/", file: "SALESF", tilde: "~1", ext: "",
	}, "https://example.test/", "Salesforce")

	if _, ok := ac.foundDirectories["Salesforce"]; !ok {
		t.Fatal("recovered extensionless path was not queued for recursive validation")
	}
}

func TestMarkResolvedFileWithExtensionNeedsDirectoryRedirect(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0}

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusOK, "ordinary file"), nil
	})}
	ac := &attackConfig{foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{})}
	br := baseRequest{url: "https://example.test/", file: "DEFAULT", tilde: "~1", ext: ".ASP"}
	markResolvedFile(ac, br, "https://example.test/", "Default.aspx")
	enrichResolvedFile(client, &httpStats{}, ac, br, "https://example.test/", "Default.aspx")

	if len(ac.foundDirectories) != 0 {
		t.Fatalf("ordinary file was queued as a directory: %#v", ac.foundDirectories)
	}
}

func TestDeferredWordlistLoadIsNonBlocking(t *testing.T) {
	opened := make(chan struct{}, 1)
	release := make(chan struct{})
	wc := newWordlistConfig([]wordlistSource{{
		name: "blocked",
		open: func() (io.ReadCloser, error) {
			opened <- struct{}{}
			<-release
			return io.NopCloser(strings.NewReader("Login.aspx\n")), nil
		},
	}})

	select {
	case <-opened:
		t.Fatal("wordlist opened before startLoading")
	default:
	}

	returned := make(chan struct{})
	go func() {
		wc.startLoading()
		close(returned)
	}()
	select {
	case <-returned:
	case <-time.After(time.Second):
		t.Fatal("startLoading blocked the caller")
	}
	select {
	case <-opened:
	case <-time.After(time.Second):
		t.Fatal("wordlist loader did not start")
	}
	close(release)
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	if len(wc.wordlist) != 1 {
		t.Fatalf("loaded %d records, want 1", len(wc.wordlist))
	}
}

func TestRainbowRecordReplacesPlainDuplicate(t *testing.T) {
	wc := newWordlistConfig([]wordlistSource{
		{
			name: "plain",
			open: func() (io.ReadCloser, error) {
				return io.NopCloser(strings.NewReader("Login.aspx\n")), nil
			},
		},
		{
			name: "rainbow",
			open: func() (io.ReadCloser, error) {
				return io.NopCloser(strings.NewReader("#SHORTSCAN#\nABCD\tLOGIN\tASP\tLogin\taspx\n")), nil
			},
		},
	})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	if len(wc.wordlist) != 1 {
		t.Fatalf("loaded %d records, want one de-duplicated record", len(wc.wordlist))
	}
	if got := wc.wordlist[0].checksums; got != "ABCD" {
		t.Fatalf("checksums = %q, want rainbow record", got)
	}
	if !wc.isRainbow || wc.loadStats.replaced != 1 || wc.loadStats.duplicates != 1 {
		t.Fatalf("unexpected load state: rainbow=%v stats=%+v", wc.isRainbow, wc.loadStats)
	}
}

func TestFilenameCandidatesWithWellKnownExtension(t *testing.T) {
	previousRegex := checksumRegex
	defer func() { checksumRegex = previousRegex }()
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	wc := newWordlistConfig([]wordlistSource{{
		name: "stems",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("Login\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	ac := &attackConfig{wordlist: wc}
	br := baseRequest{file: "LOGIN", tilde: "~1", ext: ".ASP"}
	if candidates := filenameCandidates(ac, br, false); len(candidates) != 0 {
		t.Fatalf("got %d candidates without extension expansion", len(candidates))
	}
	candidates := filenameCandidates(ac, br, true)
	found, foundDirect := false, false
	for _, candidate := range candidates {
		if candidate.record.filename+candidate.record.extension == "Login.aspx" {
			found = candidate.matchType == "well-known-extension"
		}
		if candidate.record.filename+candidate.record.extension == "LOGIN~1.aspx" {
			foundDirect = candidate.matchType == "short-name-known-extension"
		}
	}
	if !found {
		t.Fatalf("Login.aspx well-known extension candidate not found: %+v", candidates)
	}
	if !foundDirect {
		t.Fatalf("LOGIN~1.aspx direct extension candidate not found: %+v", candidates)
	}
}

func TestFilenameCandidatesPreserveExactAndChecksumMatching(t *testing.T) {
	previousRegex := checksumRegex
	defer func() { checksumRegex = previousRegex }()
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	wc := newWordlistConfig([]wordlistSource{{
		name: "rainbow",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("#SHORTSCAN#\nABCD\tDEFAUL\tASP\tDefault\taspx\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	ac := &attackConfig{wordlist: wc}
	exact := filenameCandidates(ac, baseRequest{file: "DEFAUL", tilde: "~1", ext: ".ASP"}, false)
	if len(exact) != 1 || exact[0].matchType != "wordlist" || exact[0].record.filename+exact[0].record.extension != "Default.aspx" {
		t.Fatalf("exact candidates = %+v", exact)
	}
	checksum := filenameCandidates(ac, baseRequest{file: "DEABCD", tilde: "~1", ext: ".ASP"}, false)
	if len(checksum) != 1 || checksum[0].matchType != "checksum" || checksum[0].record.filename+checksum[0].record.extension != "Default.aspx" {
		t.Fatalf("checksum candidates = %+v", checksum)
	}
}

func TestSiblingStemCandidateCrossesExtensionAndRecursiveDirectory(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{SiblingRecovery: true}

	knowledge := newSiblingStemKnowledge()
	ac := &attackConfig{siblingStems: knowledge}
	rememberConfirmedStem(ac, baseRequest{
		url: "http://example.test/", file: "COMERC", tilde: "~1", ext: "",
	}, filenameCandidate{
		record:    wordlistRecord{filename: "COMERCIAL", filename83: "COMERC"},
		matchType: "wordlist",
	}, "http://example.test/")

	target := baseRequest{
		url: "http://example.test/ENGENHARIA/", file: "COMERC", tilde: "~1", ext: ".RAR",
	}
	candidates := filenameCandidates(ac, target, false)
	if len(candidates) != 1 {
		t.Fatalf("got %d sibling candidates, want 1: %+v", len(candidates), candidates)
	}
	candidate := candidates[0]
	if got := candidate.record.filename + candidate.record.extension; got != "COMERCIAL.RAR" {
		t.Fatalf("candidate = %q, want COMERCIAL.RAR", got)
	}
	if candidate.matchType != "sibling-stem" || candidate.source != "http://example.test/COMERCIAL" {
		t.Fatalf("missing sibling provenance: %+v", candidate)
	}

	otherOrigin := target
	otherOrigin.url = "http://other.example/ENGENHARIA/"
	if candidates := filenameCandidates(ac, otherOrigin, false); len(candidates) != 0 {
		t.Fatalf("stem leaked across origins: %+v", candidates)
	}
}

func TestFrameworkManifestCandidatesPreferCanonicalProjectFiles(t *testing.T) {
	tests := []struct {
		br   baseRequest
		want string
	}{
		{baseRequest{file: "AJAXCO", tilde: "~1", ext: ".CON"}, "AjaxControlToolkit.config"},
		{baseRequest{file: "APPSET", tilde: "~1", ext: ".CON"}, "AppSettings.config"},
		{baseRequest{file: "PACKAG", tilde: "~1", ext: ".CON"}, "packages.config"},
		{baseRequest{file: "WEB", tilde: "~1", ext: ".CON"}, "web.config"},
		{baseRequest{file: "GLOBAL", tilde: "~1", ext: ".ASA"}, "Global.asax"},
	}
	for _, tt := range tests {
		candidates := frameworkManifestCandidates(tt.br)
		if len(candidates) != 1 {
			t.Fatalf("%s%s: got %d manifest candidates: %+v", tt.br.file, tt.br.ext, len(candidates), candidates)
		}
		got := candidates[0].record.filename + candidates[0].record.extension
		if got != tt.want || candidates[0].matchType != "framework-manifest" {
			t.Fatalf("%s%s: got %q (%s), want %q framework-manifest", tt.br.file, tt.br.ext, got, candidates[0].matchType, tt.want)
		}
	}
}

func TestRequestFilteredInferenceSeedsOnlyVerifiableReadableSiblings(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{SiblingRecovery: true}

	ac := &attackConfig{siblingStems: newSiblingStemKnowledge()}
	seedBR := baseRequest{url: "http://example.test/", file: "APPSET", tilde: "~1", ext: ".CON"}
	seed := filenameCandidate{
		record: wordlistRecord{
			filename: "AppSettings", extension: ".config",
			filename83: "APPSET", extension83: "CON",
		},
		matchType: "framework-manifest",
	}
	rememberInferredStem(ac, seedBR, seed, seedBR.url)

	txtBR := baseRequest{url: seedBR.url, file: "APPSET", tilde: "~1", ext: ".TXT"}
	candidates := siblingFilenameCandidates(ac, txtBR, false)
	have := make(map[string]string)
	for _, candidate := range candidates {
		have[strings.ToLower(candidate.record.filename+candidate.record.extension)] = candidate.matchType
	}
	for _, want := range []string{"AppSettings.txt", "AppSettings.Production.txt", "AppSettings.Development.txt", "AppSettings.Backup.txt"} {
		if have[strings.ToLower(want)] != "manifest-sibling-variant" {
			t.Errorf("missing actively-verifiable inferred sibling %q: %#v", want, have)
		}
	}
	// Confirming the bare stem must improve provenance without discarding the
	// manifest-derived variant expansion needed for the remaining ~2/~3 aliases.
	rememberConfirmedStem(ac, txtBR, filenameCandidate{
		record: wordlistRecord{
			filename: "AppSettings", extension: ".txt",
			filename83: "APPSET", extension83: "TXT",
		},
		matchType: "well-known-extension",
	}, txtBR.url)
	haveAfterUpgrade := make(map[string]bool)
	for _, candidate := range siblingFilenameCandidates(ac, txtBR, false) {
		haveAfterUpgrade[strings.ToLower(candidate.record.filename+candidate.record.extension)] = true
	}
	if !haveAfterUpgrade["appsettings-backup.txt"] {
		t.Fatalf("confirmed-stem upgrade discarded manifest variants: %#v", haveAfterUpgrade)
	}

	// A request-filtered extension must not be re-emitted from an inferred seed:
	// that would turn one unconfirmed guess into another unconfirmed claim.
	configBR := baseRequest{url: seedBR.url, file: "APPSET", tilde: "~1", ext: ".CON"}
	for _, candidate := range siblingFilenameCandidates(ac, configBR, true) {
		if strings.EqualFold(candidate.record.extension, ".config") {
			t.Fatalf("inferred seed generated a request-filtered .config sibling: %+v", candidate)
		}
	}
}

func TestProbeManifestSiblingReadRequiresNegativeControlAndSavesBytes(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Auto: true, Output: "human", LootDir: t.TempDir(), Retries: 0}

	var mu sync.Mutex
	var paths []string
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		mu.Lock()
		paths = append(paths, req.URL.Path)
		mu.Unlock()
		if req.URL.Path == "/AppSettings-backup.TXT" {
			return responseFor(req, http.StatusOK, "password=SYNTHETIC-SECRET"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}

	lines := probeManifestSiblingRead(client, &httpStats{}, "http://example.test/", "AppSettings-backup.TXT")
	joined := strings.Join(lines, "\n")
	if !strings.Contains(joined, "MANIFEST-SIBLING-READ/high") || !strings.Contains(joined, "saved ->") {
		t.Fatalf("controlled readable sibling was not reported/saved: %q", joined)
	}
	mu.Lock()
	defer mu.Unlock()
	controlSeen := false
	for _, p := range paths {
		if p != "/AppSettings-backup.TXT" && strings.HasSuffix(strings.ToLower(p), ".txt") {
			controlSeen = true
		}
	}
	if !controlSeen {
		t.Fatalf("read lacked a random same-extension control: %v", paths)
	}

	catchAll := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusOK, "same body for every path"), nil
	})}
	if got := probeManifestSiblingRead(catchAll, &httpStats{}, "http://example.test/", "AppSettings-backup.TXT"); len(got) != 0 {
		t.Fatalf("serve-everything control produced a disclosure: %q", got)
	}
}

func TestSiblingRecoveryRetriesAfterAliasWasObservedFirst(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache := statusCache
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache = previousStatusCache
	}()
	args = arguments{
		SiblingRecovery: true, Autocomplete: "method", Output: "human",
		Retries: 0,
	}
	var output bytes.Buffer
	outputWriter = &output
	// The "method" oracle's 405 baseline validation (statusExistsAgainstBaseline)
	// reads/writes the package-level statusCache — must be initialized here rather
	// than relying on an earlier test in the same run to have left it non-nil.
	statusCache = make(map[string]map[int]struct{})
	ac := &attackConfig{
		autocomplete:     args.Autocomplete,
		siblingStems:     newSiblingStemKnowledge(),
		foundFiles:       make(map[string]struct{}),
		foundDirectories: make(map[string]struct{}),
	}
	archiveAlias := baseRequest{
		url: "http://example.test/", file: "COMERC", tilde: "~1", ext: ".RAR",
	}
	// Simulate the concurrent enumerator finishing the archive alias before the
	// extensionless sibling has supplied its confirmed long stem.
	observeRecoveryAlias(ac, archiveAlias)
	rememberConfirmedStem(ac, baseRequest{
		url: "http://example.test/", file: "COMERC", tilde: "~1", ext: "",
	}, filenameCandidate{
		record:    wordlistRecord{filename: "COMERCIAL", filename83: "COMERC"},
		matchType: "wordlist",
	}, "http://example.test/")

	requests, aliasProbes := 0, 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests++
		if req.Method == "_" && req.URL.Path == "/COMERCIAL.RAR" {
			aliasProbes++
			return responseFor(req, http.StatusMethodNotAllowed, "confirmed archive"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	if recovered := recoverSiblingAliases(client, &httpStats{}, ac, nil); recovered != 1 {
		t.Fatalf("recovered %d sibling paths, want 1", recovered)
	}
	if _, exists := ac.foundFiles["comercial.rar"]; !exists {
		t.Fatalf("confirmed sibling path was not recorded: %#v", ac.foundFiles)
	}
	// The alias is confirmed with a single method probe; method-magic then validates
	// that 405 against a per-extension baseline (random same-extension misses, which
	// hit other paths), so the alias itself must not be re-probed.
	if aliasProbes != 1 {
		t.Fatalf("sibling recovery probed the alias %d times, want exactly 1 (of %d total)", aliasProbes, requests)
	}
	for _, want := range []string{"[SIBLING]", "status 405", "COMERC~*.RAR", "COMERCIAL.RAR", "ordinal unverified"} {
		if !strings.Contains(output.String(), want) {
			t.Errorf("output omitted %q: %q", want, output.String())
		}
	}
}

// TestSiblingRecoveryEnrichmentDoesNotSerializeOtherAliases guards against a
// real regression: markResolvedFile used to make its post-match network
// calls (probeMutations/inspectResolvedFile/the directory-redirect HEAD)
// WHILE STILL HOLDING ac.autocompleteMutex. Since every recovery pass
// (sibling, collision, reference, stem-brute, and recoverLongName itself)
// runs one goroutine per alias/candidate bounded by -c, holding that lock
// across up to ~12 sequential HTTP round-trips per match serialized every
// other concurrent goroutine on the same host behind whichever one was
// enriching a match. On a heavily-vulnerable target under --full (many
// matches) this could turn one host's scan into an effectively-unbounded
// stall with no --maxtime check catching it — reported live as a multi-host
// scan stuck at "N-1/N hosts" with throughput at 0. Fixed by splitting
// markResolvedFile (fast, lock-only) from enrichResolvedFile (network-bound,
// called after the lock is released). This test proves alias B's enrichment
// runs concurrently with alias A's — not queued behind it.
func TestSiblingRecoveryEnrichmentDoesNotSerializeOtherAliases(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache := statusCache
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache = previousStatusCache
	}()
	args = arguments{
		SiblingRecovery: true, Autocomplete: "method", Output: "human",
		Retries: 0, MutateExt: true, Concurrency: 4,
	}
	var output bytes.Buffer
	outputWriter = &output
	statusCache = make(map[string]map[int]struct{})

	ac := &attackConfig{
		autocomplete:     args.Autocomplete,
		siblingStems:     newSiblingStemKnowledge(),
		foundFiles:       make(map[string]struct{}),
		foundDirectories: make(map[string]struct{}),
	}
	aliasA := baseRequest{url: "http://example.test/", file: "COMERC", tilde: "~1", ext: ".RAR"}
	aliasB := baseRequest{url: "http://example.test/", file: "SECOND", tilde: "~1", ext: ".TXT"}
	observeRecoveryAlias(ac, aliasA)
	observeRecoveryAlias(ac, aliasB)
	rememberConfirmedStem(ac, baseRequest{url: "http://example.test/", file: "COMERC", tilde: "~1", ext: ""},
		filenameCandidate{record: wordlistRecord{filename: "COMERCIAL", filename83: "COMERC"}, matchType: "wordlist"},
		"http://example.test/")
	rememberConfirmedStem(ac, baseRequest{url: "http://example.test/", file: "SECOND", tilde: "~1", ext: ""},
		filenameCandidate{record: wordlistRecord{filename: "SECONDARY", filename83: "SECOND"}, matchType: "wordlist"},
		"http://example.test/")

	aEnteredEnrichment := make(chan struct{})
	var aSignalOnce sync.Once
	release := make(chan struct{})
	bEnrichmentSeen := make(chan struct{})
	var bSignalOnce sync.Once
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		switch {
		case req.Method == "_" && req.URL.Path == "/COMERCIAL.RAR":
			return responseFor(req, http.StatusMethodNotAllowed, "confirmed A"), nil
		case req.Method == "_" && req.URL.Path == "/SECONDARY.TXT":
			// Force ordering: don't let B's own existence check resolve until A
			// is confirmed to be inside its (blocked) enrichment call — otherwise
			// B could race ahead and finish before A even gets there, passing
			// vacuously regardless of whether the lock-scope fix is present.
			<-aEnteredEnrichment
			return responseFor(req, http.StatusMethodNotAllowed, "confirmed B"), nil
		case req.Method == "_":
			return responseFor(req, http.StatusNotFound, "missing"), nil
		case req.Method == "GET" && strings.Contains(req.URL.Path, "COMERCIAL.RAR"):
			// Alias A's post-match enrichment (probeMutations). Signals it has
			// started, then blocks until the test has observed B's own
			// enrichment running concurrently.
			aSignalOnce.Do(func() { close(aEnteredEnrichment) })
			<-release
			return responseFor(req, http.StatusNotFound, "no mutation"), nil
		case req.Method == "GET" && strings.Contains(req.URL.Path, "SECONDARY.TXT"):
			bSignalOnce.Do(func() { close(bEnrichmentSeen) })
			return responseFor(req, http.StatusNotFound, "no mutation"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}

	done := make(chan int, 1)
	go func() { done <- recoverSiblingAliases(client, &httpStats{}, ac, nil) }()

	select {
	case <-bEnrichmentSeen:
		// Good: B's enrichment fired while A's is still blocked below.
	case <-time.After(2 * time.Second):
		t.Fatal("alias B's enrichment never ran while alias A was blocked — recovery passes are serializing on a shared lock across markResolvedFile's network calls")
	}
	close(release)

	if recovered := <-done; recovered != 2 {
		t.Fatalf("recovered %d sibling paths, want 2", recovered)
	}
}

// TestSiblingRecoveryRespectsMaxTime proves recoverSiblingAliases stops
// starting new aliases once the caller's timedOut closure trips — the
// --maxtime soft budget (cli.go) that Scan() already applies between queued
// top-level paths, threaded into this pass so a scan long enough to matter
// has a circuit breaker even where the lock-scope fix above doesn't apply
// (e.g. a target that's merely slow to answer, not stuck on the bug it
// guards against).
func TestSiblingRecoveryRespectsMaxTime(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache := statusCache
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache = previousStatusCache
	}()
	args = arguments{SiblingRecovery: true, Autocomplete: "method", Output: "human", Retries: 0, Concurrency: 1}
	outputWriter = io.Discard
	statusCache = make(map[string]map[int]struct{})

	ac := &attackConfig{
		autocomplete:     args.Autocomplete,
		siblingStems:     newSiblingStemKnowledge(),
		foundFiles:       make(map[string]struct{}),
		foundDirectories: make(map[string]struct{}),
	}
	for _, name := range []string{"AAAAAA", "BBBBBB", "CCCCCC"} {
		observeRecoveryAlias(ac, baseRequest{url: "http://example.test/", file: name[:6], tilde: "~1", ext: ".TXT"})
		rememberConfirmedStem(ac, baseRequest{url: "http://example.test/", file: name[:6], tilde: "~1", ext: ""},
			filenameCandidate{record: wordlistRecord{filename: name + "STEM", filename83: name[:6]}, matchType: "wordlist"},
			"http://example.test/")
	}

	probed := make(map[string]struct{})
	var probedMu sync.Mutex
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.Method == "_" {
			probedMu.Lock()
			probed[req.URL.Path] = struct{}{}
			probedMu.Unlock()
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	// Trips immediately: with Concurrency 1, the very first alias still starts
	// (the check runs before starting each one, not mid-flight), but the
	// second and third must not.
	calls := 0
	timedOut := func() bool { calls++; return calls > 1 }
	recoverSiblingAliases(client, &httpStats{}, ac, timedOut)

	if calls == 0 {
		t.Fatal("timedOut was never checked")
	}
	if len(probed) >= 3 {
		t.Fatalf("all 3 aliases were probed despite timedOut tripping after the first: %v", probed)
	}
}

func TestStatusAutocompleteDoesNotReadArchiveBodies(t *testing.T) {
	previousArgs := args
	previousStatusCache := statusCache
	defer func() {
		args = previousArgs
		statusCache = previousStatusCache
	}()
	args = arguments{Autocomplete: "status", Retries: 0}
	statusCache = make(map[string]map[int]struct{})
	reads, closes := 0, 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		status := http.StatusNotFound
		if req.URL.Path == "/COMERCIAL.RAR" {
			status = http.StatusOK
		}
		return &http.Response{
			StatusCode: status, Status: http.StatusText(status), Header: make(http.Header),
			Body: trackingBody{reads: &reads, closes: &closes}, Request: req,
		}, nil
	})}
	candidate := filenameCandidate{record: wordlistRecord{filename: "COMERCIAL", extension: ".RAR"}}
	res, matched, err := probeAutocompleteCandidate(client, &httpStats{}, &attackConfig{autocomplete: args.Autocomplete}, baseRequest{
		url: "http://example.test/", file: "COMERC", tilde: "~1", ext: ".RAR",
	}, "http://example.test/", candidate)
	if err != nil || !matched || res.StatusCode != http.StatusOK {
		t.Fatalf("status autocomplete failed: status=%v matched=%v err=%v", res, matched, err)
	}
	if reads != 0 {
		t.Fatalf("status-only recovery read response bodies %d times", reads)
	}
	// 1 candidate + 2 initial baseline + statusEscalateSamples (10) escalation probes:
	// an apparent hit (200, absent from the small baseline) is always confirmed
	// against a larger sample before being trusted (see statusExistsAgainstBaseline).
	if want := 1 + 2 + statusEscalateSamples; closes != want {
		t.Fatalf("closed %d bodies, want %d (candidate + baseline + escalation)", closes, want)
	}
}

func TestShortAliasHitDoesNotSeedSiblingStem(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{SiblingRecovery: true}
	ac := &attackConfig{siblingStems: newSiblingStemKnowledge()}
	br := baseRequest{url: "http://example.test/", file: "COMERC", tilde: "~1", ext: ".RAR"}
	rememberConfirmedStem(ac, br, filenameCandidate{
		record:    wordlistRecord{filename: "COMERC~1", extension: ".RAR"},
		matchType: "short-name",
	}, "http://example.test/")
	if candidates := siblingFilenameCandidates(ac, br, false); len(candidates) != 0 {
		t.Fatalf("literal alias was learned as a long stem: %+v", candidates)
	}
}

func TestParseStatusCodes(t *testing.T) {
	statuses, err := parseStatusCodes("200,204,300-302")
	if err != nil {
		t.Fatalf("parseStatusCodes: %v", err)
	}
	for _, status := range []int{200, 204, 300, 301, 302} {
		if _, exists := statuses[status]; !exists {
			t.Errorf("status %d missing", status)
		}
	}
	if _, err := parseStatusCodes("99-200"); err == nil {
		t.Fatal("invalid range accepted")
	}
}

func TestSameFilePath(t *testing.T) {
	if !sameFilePath("./candidates.txt", "candidates.txt") {
		t.Fatal("equivalent relative paths were not detected")
	}
	if sameFilePath("candidates.txt", "wordlist.txt") {
		t.Fatal("different paths were treated as equal")
	}
}

// beginSection must not divide before the first section in a block (the
// headerRule + blank line already did that job) but must divide before
// every section after it — one rule per boundary, not one per section.
func TestBeginSectionOnlyDividesAfterFirst(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	args = arguments{Output: "human"}
	var output bytes.Buffer
	outputWriter = &output

	ac := &attackConfig{}
	beginSection(ac)
	if strings.Contains(output.String(), sectionRule) {
		t.Fatalf("first section printed a divider: %q", output.String())
	}
	beginSection(ac)
	if got := strings.Count(output.String(), sectionRule); got != 1 {
		t.Fatalf("second section: want 1 divider printed so far, got %d: %q", got, output.String())
	}
	beginSection(ac)
	if got := strings.Count(output.String(), sectionRule); got != 2 {
		t.Fatalf("third section: want 2 dividers printed so far, got %d: %q", got, output.String())
	}
	if !ac.sectionStarted {
		t.Fatal("sectionStarted should be true after beginSection has run")
	}
}

func TestBeginSectionNilSafe(t *testing.T) {
	beginSection(nil) // must not panic
}

func TestNonVulnerableScanDoesNotOpenWordlist(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousRegex := checksumRegex
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		checksumRegex = previousRegex
	}()
	args = arguments{
		Autocomplete: "status", Output: "human", Patience: 0, Characters: "A",
		Concurrency: 1, Retries: 1, RetryDelay: 1, TildeEncoding: "default",
	}
	outputWriter = io.Discard
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	opened := false
	wc := newWordlistConfig([]wordlistSource{{
		name: "should-not-open",
		open: func() (io.ReadCloser, error) {
			opened = true
			return io.NopCloser(strings.NewReader("Login.aspx\n")), nil
		},
	}})
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	Scan([]string{"http://example.test"}, client, &httpStats{}, wc, markers{}, make(map[string]struct{}))
	if opened {
		t.Fatal("non-vulnerable target caused wordlist parsing")
	}
}

// A reserved folder (bin, App_Code, App_Data) is a requestFiltering hiddenSegment: an
// ordinary GET on it 404s for everything, so it never shows 8.3-oracle signal on its own
// (ac.tildes stays empty) and the scan takes the non-vulnerable early return. -i/--full
// exist precisely to reach around that via ::$INDEX_ALLOCATION, so the sweep must still be
// enqueued from that early-return path — not only from the code reachable exclusively when
// the directory already looked vulnerable by ordinary means.
func TestNonVulnerableReservedFolderStillEnqueuesIndexChain(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousRegex := checksumRegex
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		checksumRegex = previousRegex
	}()
	args = arguments{
		Autocomplete: "status", Output: "human", Patience: 0, Characters: "A",
		Concurrency: 1, Retries: 1, RetryDelay: 1, TildeEncoding: "default",
		Index: true, Auto: true,
	}
	outputWriter = io.Discard
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	visited := make(map[string]struct{})
	Scan([]string{"http://example.test/bin"}, client, &httpStats{}, newWordlistConfig(nil), markers{}, visited)
	if _, ok := visited["http://example.test/bin::$index_allocation/"]; !ok {
		t.Fatalf("scanning a reserved folder directly did not enqueue its ::$INDEX_ALLOCATION probe: visited=%#v", visited)
	}
}

func TestTransientInfraStatus(t *testing.T) {
	for _, c := range []int{429, 502, 503, 504} {
		if !isTransientInfraStatus(c) {
			t.Errorf("%d should be transient-infra", c)
		}
	}
	// 500 and 501 are real IIS answers: a stable 500 baseline (DEBUG neg=500,
	// pos=404 on a real live target) is a legitimate oracle, and 501 anchors a
	// TRACE/method oracle. Neither may be blanket-banned; a FLAPPING 500 is caught
	// by probeOracleCombo's negative-baseline re-verify instead.
	for _, c := range []int{200, 301, 400, 403, 404, 405, 500, 501} {
		if isTransientInfraStatus(c) {
			t.Errorf("%d must NOT be transient-infra (it's a real IIS answer)", c)
		}
	}
}

// TestFlappingDebugBaselineRejected is the regression guard for a live false positive: the
// DEBUG verb's baseline (/*<digit>*) bounces 400/500, so the 4-probe calibration can
// catch a 500 burst and pair it against a 400 positive - a phantom oracle. The
// negative-baseline re-verify must reject it (neg re-probes come back 400 != 500).
func TestFlappingDebugBaselineRejected(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0}
	var calls int
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if strings.Contains(req.URL.Path, "~0") { // ~0 guard differs from pos so the guard PASSES; the re-verify must be what catches the flap
			return responseFor(req, http.StatusInternalServerError, "guard"), nil
		}
		if strings.Contains(req.URL.Path, "~") { // ~1..~4 positive -> 400
			return responseFor(req, http.StatusBadRequest, "no"), nil
		}
		// negative baseline /*<digit>*: first 4 (calibration) are a 500 burst, then
		// it flaps back to 400 - exactly what the re-verify must catch.
		calls++
		if calls <= 4 {
			return responseFor(req, http.StatusInternalServerError, "err"), nil
		}
		return responseFor(req, http.StatusBadRequest, "no"), nil
	})}
	r := probeOracleCombo(client, &httpStats{}, "http://example.test/", "DEBUG", "")
	if len(r.tildes) != 0 {
		t.Errorf("a flapping 500 baseline must NOT fabricate a tilde oracle, got tildes=%v", r.tildes)
	}
	if !r.flapped {
		t.Errorf("a rejected flap should mark the combo flapped, got %+v", r)
	}
}

// TestStable500BaselineOracleAccepted is the regression guard for the fix that broke
// a real target: a genuinely enumerable IIS host answers the DEBUG verb 500 for a
// missing 8.3 and 404 for an existing one, EVERY time. That stable 500 baseline is a
// real oracle and must be accepted (blanket-banning 500 wrongly suppressed it).
func TestStable500BaselineOracleAccepted(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0}
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		// ~1..~4 -> 404 (exists); ~0 guard -> 500 (missing, != pos); neg -> 500 always.
		if strings.Contains(req.URL.Path, "~0") {
			return responseFor(req, http.StatusInternalServerError, "missing"), nil
		}
		if strings.Contains(req.URL.Path, "~") {
			return responseFor(req, http.StatusNotFound, "exists"), nil
		}
		return responseFor(req, http.StatusInternalServerError, "missing"), nil
	})}
	r := probeOracleCombo(client, &httpStats{}, "http://example.test/", "DEBUG", "")
	if len(r.tildes) == 0 {
		t.Fatalf("a STABLE 500 baseline with a 404 positive is a real oracle and must be accepted, got %+v", r)
	}
	if r.statusNeg != http.StatusInternalServerError || r.statusPos != http.StatusNotFound {
		t.Errorf("oracle statuses wrong: statusNeg=%d statusPos=%d, want 500/404", r.statusNeg, r.statusPos)
	}
}

func TestMixedPositiveStatusesAreTypedPerTilde(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0}
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		switch {
		case strings.Contains(req.URL.Path, "~0"):
			return responseFor(req, http.StatusOK, "missing"), nil
		case strings.Contains(req.URL.Path, "~1"):
			return responseFor(req, http.StatusNotFound, "first stratum"), nil
		case strings.Contains(req.URL.Path, "~2"):
			return responseFor(req, http.StatusForbidden, "second stratum"), nil
		case strings.Contains(req.URL.Path, "~"):
			return responseFor(req, http.StatusOK, "missing"), nil
		default:
			return responseFor(req, http.StatusOK, "missing"), nil
		}
	})}

	r := probeOracleCombo(client, &httpStats{}, "http://example.test/", "OPTIONS", "/")
	if got, want := strings.Join(r.tildes, ","), "~1,~2"; got != want {
		t.Fatalf("tildes=%q, want %q", got, want)
	}
	first, ok := r.markersByTilde["~1"]
	if !ok || first.statusPos != http.StatusNotFound || first.statusNeg != http.StatusOK {
		t.Fatalf("~1 markers=%+v, want pos=404 neg=200", first)
	}
	second, ok := r.markersByTilde["~2"]
	if !ok || second.statusPos != http.StatusForbidden || second.statusNeg != http.StatusOK {
		t.Fatalf("~2 markers=%+v, want pos=403 neg=200", second)
	}
	if responseMatchesPositive(responseFor(nil, http.StatusForbidden, "wrong stratum"), first) {
		t.Fatal("~1/404 profile cross-accepted ~2/403 response")
	}
	if responseMatchesPositive(responseFor(nil, http.StatusNotFound, "wrong stratum"), second) {
		t.Fatal("~2/403 profile cross-accepted ~1/404 response")
	}
	if !responseMatchesPositive(responseFor(nil, http.StatusNotFound, "first"), first) {
		t.Fatal("~1/404 profile rejected its own signature")
	}
	if !responseMatchesPositive(responseFor(nil, http.StatusForbidden, "second"), second) {
		t.Fatal("~2/403 profile rejected its own signature")
	}
}

// TestFlappingFrontendYieldsNoPhantomOracle locks in the fix for the live GCLB /
// Cloud Armor case: a load balancer fans identical probes to backends whose
// health flaps, so the SAME 8.3 probe returns 503, 404, 503, 503, 404, … The
// negative baseline (no tilde) is a stable real 404, but the ~i positive hits a
// 503 backend — and, crucially, the ~0 catch-all guard hits a healthy 404, so the
// old code accepted a phantom positive (statusPos=503 != statusNeg=404) and
// exploded into hundreds of never-resolving names. The fix must refuse to anchor
// the oracle on a 5xx/429, report the flapping front end, and emit ZERO
// short names.
func TestFlappingFrontendYieldsNoPhantomOracle(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
	}()
	args = arguments{
		Autocomplete: "status", Output: "human", Patience: 0, Characters: "AB",
		Concurrency: 1, Retries: 0, RetryDelay: 1, TildeEncoding: "default",
	}
	var out bytes.Buffer
	outputWriter = &out
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)

	// Backend health flap: a tilde-positive probe (~1..~4) lands on an unhealthy
	// backend (503), while the negative baseline and the ~0 guard land on a healthy
	// one (404). This is exactly the shape that defeats the ~0 catch-all guard.
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		p := strings.ToLower(req.URL.EscapedPath())
		hasZero := strings.Contains(p, "~0") || strings.Contains(p, "%7e0")
		hasTilde := strings.Contains(p, "~") || strings.Contains(p, "%7e")
		if hasTilde && !hasZero {
			return responseFor(req, http.StatusServiceUnavailable, "backend flap"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	Scan([]string{"http://gclb.test/"}, client, &httpStats{}, newWordlistConfig(nil), markers{}, make(map[string]struct{}))

	s := out.String()
	if !strings.Contains(s, "flapping front end") {
		t.Fatalf("expected the flapping-front-end warning, got:\n%s", s)
	}
	if strings.Contains(s, "~2") || strings.Contains(s, "SHORTNAMES") || strings.Contains(s, "Vulnerable: Yes") {
		t.Fatalf("flapping front end must not manufacture a phantom oracle / short names, got:\n%s", s)
	}
}

// IIS/NTFS paths are case-insensitive, so two queued URLs differing only in
// case (e.g. the 8.3 wordlist's canonical "ASPNET_CLIENT" vs WebDAV's
// on-disk "aspnet_client") name the same physical directory and must dedup
// to a single scan — otherwise every directory recursively found under each
// casing gets scanned twice again, compounding at each recursion level.
func TestScanDedupsCaseInsensitively(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
	}()
	args = arguments{
		Autocomplete: "status", Output: "human", Patience: 0, Characters: "A",
		Concurrency: 1, Retries: 1, RetryDelay: 1, TildeEncoding: "default",
	}
	outputWriter = io.Discard
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	visited := make(map[string]struct{})
	Scan([]string{"http://example.test/Dir", "http://example.test/dir"}, client, &httpStats{}, newWordlistConfig(nil), markers{}, visited)
	if len(visited) != 1 {
		t.Fatalf("visited has %d entries after two case-variant URLs, want 1: %#v", len(visited), visited)
	}
}

func TestBruteForcePromotesOnlyStatusDifferential(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousRegex, previousBruteStatuses := checksumRegex, bruteStatuses
	previousCandidateWriter := candidateOutputWriter
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		checksumRegex, bruteStatuses = previousRegex, previousBruteStatuses
		candidateOutputWriter = previousCandidateWriter
	}()
	args = arguments{
		Autocomplete: "none", Output: "human", ProbeCandidates: true, ProbeStatus: "200",
		Retries: 1, RetryDelay: 1,
	}
	outputWriter = io.Discard
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	bruteStatuses = map[int]struct{}{http.StatusOK: {}}
	candidateOutputWriter = nil
	wc := newWordlistConfig([]wordlistSource{{
		name: "stems",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("Login\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.URL.Path == "/Login.aspx" {
			return responseFor(req, http.StatusOK, "hit"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	ac := &attackConfig{
		wordlist: wc, foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{}),
	}
	match := recoverLongName(client, &httpStats{}, ac, baseRequest{
		url: "http://example.test/", file: "LOGIN", tilde: "~1", ext: ".ASP",
	})
	if match.path != "Login.aspx" || match.status != http.StatusOK || match.matchType != "well-known-extension" {
		t.Fatalf("unexpected match: %+v", match)
	}
	if len(ac.foundFiles) != 1 {
		t.Fatalf("reported %d brute-force hits, want 1", len(ac.foundFiles))
	}
}

func TestBruteForceReportsLongNamesAsCollisionGroup(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousRegex, previousBruteStatuses := checksumRegex, bruteStatuses
	previousCandidateWriter := candidateOutputWriter
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		checksumRegex, bruteStatuses = previousRegex, previousBruteStatuses
		candidateOutputWriter = previousCandidateWriter
	}()
	args = arguments{
		Autocomplete: "none", Output: "human", ProbeCandidates: true, ProbeStatus: "200",
		Retries: 0,
	}
	var output bytes.Buffer
	outputWriter = &output
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	bruteStatuses = map[int]struct{}{http.StatusOK: {}}
	candidateOutputWriter = nil
	wc := newWordlistConfig([]wordlistSource{{
		name: "collisions",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("PagedList.dll\nPagedList.Mvc.dll\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	requests := make(map[string]int)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests[req.URL.Path]++
		switch req.URL.Path {
		case "/PagedList.dll", "/PagedList.Mvc.dll":
			return responseFor(req, http.StatusOK, "hit"), nil
		case "/PAGEDL~1.DLL", "/PAGEDL~2.DLL":
			return responseFor(req, http.StatusBadRequest, "alias blocked"), nil
		default:
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
	})}
	ac := &attackConfig{
		wordlist: wc, foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{}),
	}
	match := recoverLongName(client, &httpStats{}, ac, baseRequest{
		url: "http://example.test/", file: "PAGEDL", tilde: "~1", ext: ".DLL",
	})
	if match.collisionGroup != "PAGEDL~*.DLL" || match.ordinalVerified {
		t.Fatalf("unexpected collision metadata: %+v", match)
	}
	if len(ac.foundFiles) != 2 {
		t.Fatalf("recovered %d long names, want both collision candidates", len(ac.foundFiles))
	}
	for _, name := range []string{"PagedList.dll", "PagedList.Mvc.dll"} {
		if !strings.Contains(output.String(), name) {
			t.Errorf("recovery output omitted %s: %q", name, output.String())
		}
	}
	if !strings.Contains(output.String(), "PAGEDL~*.DLL") || !strings.Contains(output.String(), "ordinal unverified") {
		t.Fatalf("collision caveat missing from output: %q", output.String())
	}

	// A second observed ordinal still gets its literal alias probe, but must
	// not re-run the shared long-name candidate set.
	_ = recoverLongName(client, &httpStats{}, ac, baseRequest{
		url: "http://example.test/", file: "PAGEDL", tilde: "~2", ext: ".DLL",
	})
	if requests["/PagedList.dll"] != 1 || requests["/PagedList.Mvc.dll"] != 1 {
		t.Fatalf("long-name collision group was probed more than once: %#v", requests)
	}
	if requests["/PAGEDL~1.DLL"] != 1 || requests["/PAGEDL~2.DLL"] != 1 {
		t.Fatalf("literal aliases were not probed individually: %#v", requests)
	}
}

func TestBruteForceDistanceOracleFindsSameStatusBodyDifferential(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousRegex, previousBruteStatuses := checksumRegex, bruteStatuses
	previousCandidateWriter := candidateOutputWriter
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		checksumRegex, bruteStatuses = previousRegex, previousBruteStatuses
		candidateOutputWriter = previousCandidateWriter
	}()
	args = arguments{
		Autocomplete: "none", Output: "human", ProbeCandidates: true, ProbeStatus: "404",
		ProbeOracle: "distance", ProbeMethod: "OPTIONS", ProbeSuffix: "/~1.rem",
		ProbeBodyLimit: 4096, Retries: 0,
	}
	var output bytes.Buffer
	outputWriter = &output
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	bruteStatuses = map[int]struct{}{http.StatusNotFound: {}}
	candidateOutputWriter = nil
	wc := newWordlistConfig([]wordlistSource{{
		name: "exact",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("PagedList.dll\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	requestMethods := make(map[string]int)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requestMethods[req.Method]++
		if req.URL.Path == "/PagedList.dll/~1.rem" {
			return responseFor(req, http.StatusNotFound, "<html><title>IIS native file block</title><p>resource exists but is forbidden</p></html>"), nil
		}
		body := strings.Repeat("custom application route not found ", 30) + req.URL.Path
		return responseFor(req, http.StatusNotFound, body), nil
	})}
	ac := &attackConfig{
		wordlist: wc, foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{}),
	}
	match := recoverLongName(client, &httpStats{}, ac, baseRequest{
		url: "http://example.test/", file: "PAGEDL", tilde: "~1", ext: ".DLL",
	})
	if match.path != "PagedList.dll" || match.status != http.StatusNotFound {
		t.Fatalf("same-status body differential was not recovered: %+v", match)
	}
	if match.oracle != "distance" || match.method != "OPTIONS" || match.suffix != "/~1.rem" {
		t.Fatalf("probe provenance missing: %+v", match)
	}
	if requestMethods["OPTIONS"] == 0 || len(requestMethods) != 1 {
		t.Fatalf("unexpected probe methods: %#v", requestMethods)
	}
	if len(ac.foundFiles) != 1 {
		t.Fatalf("distance oracle reported %d files, want only the native-body hit", len(ac.foundFiles))
	}
	if !strings.Contains(output.String(), "distance/OPTIONS") || !strings.Contains(output.String(), `suffix="/~1.rem"`) {
		t.Fatalf("probe profile missing from human output: %q", output.String())
	}
}

func TestDistanceOracleDoesNotPromoteUnderSampledBaseline(t *testing.T) {
	dists := map[int]distances{
		http.StatusNotFound: {body: "one control only", samples: 1},
	}
	if matched, _, _ := differsFromDistanceBaseline(http.StatusNotFound, []byte("very different candidate"), dists); matched {
		t.Fatal("distance oracle promoted a candidate with only one same-status control")
	}
	if matched, _, _ := differsFromDistanceBaseline(http.StatusForbidden, []byte("candidate"), dists); matched {
		t.Fatal("distance oracle promoted a status differential with only one successful control")
	}
	stableControls := map[int]distances{
		http.StatusNotFound: {body: "stable controls", samples: 2},
	}
	if matched, _, _ := differsFromDistanceBaseline(http.StatusForbidden, []byte("candidate"), stableControls); !matched {
		t.Fatal("status absent from all controls was not treated as a differential")
	}
}

func TestStatusAutocompleteStillRecoversExactWordlistMatch(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousRegex := checksumRegex
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		checksumRegex = previousRegex
	}()
	args = arguments{Autocomplete: "status", Output: "human", Retries: 0}
	outputWriter = io.Discard
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	wc := newWordlistConfig([]wordlistSource{{
		name: "exact",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("Login.aspx\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.URL.Path == "/Login.aspx" {
			return responseFor(req, http.StatusOK, "hit"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	ac := &attackConfig{autocomplete: args.Autocomplete, wordlist: wc, foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{})}
	match := recoverLongName(client, &httpStats{}, ac, baseRequest{
		url: "http://example.test/", file: "LOGIN", tilde: "~1", ext: ".ASP",
	})
	if match.path != "Login.aspx" || match.matchType != "wordlist" || match.status != http.StatusOK {
		t.Fatalf("unexpected autocomplete match: %+v", match)
	}
}

func TestCandidateOutputDoesNotProbe(t *testing.T) {
	previousArgs, previousCandidateWriter := args, candidateOutputWriter
	previousCandidateSeen := candidateOutputSeen
	defer func() {
		args, candidateOutputWriter, candidateOutputSeen = previousArgs, previousCandidateWriter, previousCandidateSeen
	}()
	args = arguments{Autocomplete: "none", Output: "human"}
	var output bytes.Buffer
	candidateOutputWriter = &output
	candidateOutputSeen = make(map[string]struct{})
	wc := newWordlistConfig([]wordlistSource{{
		name: "stems",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("Login\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	ac := &attackConfig{autocomplete: args.Autocomplete, wordlist: wc, foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{})}
	match := recoverLongName(nil, &httpStats{}, ac, baseRequest{url: "https://example.test/", file: "LOGIN", tilde: "~1", ext: ".ASP"})
	if match.path != "" {
		t.Fatalf("candidate-only export unexpectedly confirmed a hit: %+v", match)
	}
	if !strings.Contains(output.String(), "https://example.test/Login.aspx\n") {
		t.Fatalf("candidate URL missing from output: %q", output.String())
	}
}

func TestCSVRecoveryIncludesCollisionAndProbeProvenance(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousHeader := csvHeaderPrinted
	defer func() {
		args, outputWriter, csvHeaderPrinted = previousArgs, previousWriter, previousHeader
	}()
	args = arguments{Output: "csv"}
	var output bytes.Buffer
	outputWriter = &output
	csvHeaderPrinted = false
	verified := false
	printJSON(resultOutput{
		Type: "recovery", FullMatch: true, BaseUrl: "https://example.test/",
		File: "PAGEDL", Tilde: "~1", Ext: ".DLL", Fullname: "PagedList.dll",
		MatchType: "wordlist", Status: http.StatusNotFound,
		CollisionGroup: "PAGEDL~*.DLL", OrdinalVerified: &verified,
		Oracle: "distance", Method: "OPTIONS", ProbeSuffix: "/~1.rem",
	})
	got := output.String()
	if !strings.Contains(got, "collisiongroup,ordinalverified,oracle,method,probesuffix") {
		t.Fatalf("CSV header omitted recovery provenance: %q", got)
	}
	if !strings.Contains(got, `"PAGEDL~*.DLL","false","distance","OPTIONS","/~1.rem"`) {
		t.Fatalf("CSV row omitted recovery provenance: %q", got)
	}
}

// TestStructuredOutputCarriesDirectoryConfirmed locks in JSON/CSV parity with the
// human "[DIR]" annotation added for the auto-dirconfirm feature: structured-
// output consumers (json/ndjson/csv) get the same signal via a dedicated
// "directoryconfirmed" field instead of a rendered tag, so automation doesn't
// have to string-match the human line.
func TestStructuredOutputCarriesDirectoryConfirmed(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()

	args = arguments{Output: "json"}
	var jsonOut bytes.Buffer
	outputWriter = &jsonOut
	printJSON(resultOutput{
		Type: "result", BaseUrl: "https://example.test/",
		File: "WILDCA", Tilde: "~1", Partname: "WILDCA?",
		DirectoryConfirmed: true,
	})
	if !strings.Contains(jsonOut.String(), `"directoryconfirmed":true`) {
		t.Fatalf("JSON must carry directoryconfirmed=true, got %q", jsonOut.String())
	}

	previousHeader := csvHeaderPrinted
	defer func() { csvHeaderPrinted = previousHeader }()
	args = arguments{Output: "csv"}
	var csvOut bytes.Buffer
	outputWriter = &csvOut
	csvHeaderPrinted = false
	printJSON(resultOutput{
		Type: "result", BaseUrl: "https://example.test/",
		File: "WILDCA", Tilde: "~1", Partname: "WILDCA?",
		DirectoryConfirmed: true,
	})
	got := csvOut.String()
	if !strings.Contains(got, "canonicalguardbypasscandidate,directoryconfirmed,sensitivereason") {
		t.Fatalf("CSV header must include directoryconfirmed and sensitivereason, got %q", got)
	}
	if !strings.HasSuffix(strings.TrimRight(got, "\n"), `,true,""`) {
		t.Fatalf("CSV row must end with directoryconfirmed=true, sensitivereason=\"\", got %q", got)
	}
}

// TestStructuredOutputCarriesSensitiveReason locks in JSON/CSV parity with the human
// "[SENSITIVE]" annotation: structured-output consumers get the same signal via a
// dedicated "sensitivereason" field instead of a rendered tag.
func TestStructuredOutputCarriesSensitiveReason(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()

	const reason = "archive — possible source/backup"

	args = arguments{Output: "json"}
	var jsonOut bytes.Buffer
	outputWriter = &jsonOut
	printJSON(resultOutput{
		Type: "result", BaseUrl: "https://example.test/",
		File: "BACKUP", Tilde: "~1", Ext: "ZIP", Fullname: "backup.zip",
		SensitiveReason: reason,
	})
	if !strings.Contains(jsonOut.String(), `"sensitivereason":"`+reason+`"`) {
		t.Fatalf("JSON must carry sensitivereason, got %q", jsonOut.String())
	}

	previousHeader := csvHeaderPrinted
	defer func() { csvHeaderPrinted = previousHeader }()
	args = arguments{Output: "csv"}
	var csvOut bytes.Buffer
	outputWriter = &csvOut
	csvHeaderPrinted = false
	printJSON(resultOutput{
		Type: "result", BaseUrl: "https://example.test/",
		File: "BACKUP", Tilde: "~1", Ext: "ZIP", Fullname: "backup.zip",
		SensitiveReason: reason,
	})
	got := csvOut.String()
	if !strings.HasSuffix(strings.TrimRight(got, "\n"), `,"`+reason+`"`) {
		t.Fatalf("CSV row must end with sensitivereason=%q, got %q", reason, got)
	}
}

// helper for older Go versions without builtin min()
func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

// TestWordlistCarriesLeakedVSProjectFolders locks in the bundled-wordlist coverage
// added after a real scan hit a leaked Visual Studio project folder: PublishProfiles
// (the extensionless directory that holds *.pubxml deployment secrets — publish URL,
// MSDeploy credentials, connection strings) and the ASP.NET Core secrets configs.
// Before these entries existed, PUBLIS~1 stayed unresolved and the tool never
// recursed into the PublishProfiles subtree where the secret .pubxml lives.
func TestWordlistCarriesLeakedVSProjectFolders(t *testing.T) {
	wc, err := configureWordlists(nil) // embedded resources/wordlist.txt
	if err != nil {
		t.Fatalf("configureWordlists: %v", err)
	}
	wc.startLoading()
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	hasExtensionless := func(f83, want string) bool {
		for _, r := range wc.candidatesByFilename83(f83) {
			if r.extension83 == "" && strings.EqualFold(r.filename, want) {
				return true
			}
		}
		return false
	}
	// the loaded record stores the extension WITH a leading dot (".json").
	hasFull := func(f83, wantName, wantExt string) bool {
		for _, r := range wc.candidatesByFilename83(f83) {
			if strings.EqualFold(r.filename, wantName) &&
				strings.EqualFold(strings.TrimPrefix(r.extension, "."), wantExt) {
				return true
			}
		}
		return false
	}
	if !hasExtensionless("PUBLIS", "PublishProfiles") {
		t.Error("bundled wordlist must resolve PUBLIS~1 -> PublishProfiles (extensionless dir)")
	}
	if !hasFull("APPSET", "appsettings.Production", "json") {
		t.Error("bundled wordlist must carry appsettings.Production.json")
	}
	if !hasFull("SECRET", "secrets", "json") {
		t.Error("bundled wordlist must carry secrets.json")
	}
}
