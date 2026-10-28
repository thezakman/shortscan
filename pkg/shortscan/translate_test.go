package shortscan

import (
	"bytes"
	"io"
	"net/http"
	"regexp"
	"strings"
	"testing"
)

func TestTranslateOracleUsesHeaderAndStableControls(t *testing.T) {
	previousArgs, previousBaselines := args, translateBaselines
	defer func() { args, translateBaselines = previousArgs, previousBaselines }()
	args = arguments{Retries: 0}
	translateBaselines = make(map[string]translateBaseline)

	requests := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests++
		if req.Method != http.MethodGet || req.Header.Get("Translate") != "f" || req.Header.Get("Cache-Control") != "no-cache" {
			t.Fatalf("unexpected Translate request: method=%q headers=%#v", req.Method, req.Header)
		}
		status := http.StatusNotFound
		if req.URL.Path == "/srcpage.aspx" {
			status = http.StatusUnauthorized
		}
		return responseFor(req, status, ""), nil
	})}

	res, matched, err := translateExistsAgainstBaseline(client, &httpStats{}, "http://example.test/", "srcpage.aspx", "", ".aspx")
	if err != nil {
		t.Fatal(err)
	}
	if !matched || res.StatusCode != http.StatusUnauthorized {
		t.Fatalf("Translate differential not accepted: matched=%v response=%#v", matched, res)
	}
	if requests != 6 {
		t.Fatalf("got %d requests, want candidate + 2 controls + full repeat", requests)
	}
}

func TestTranslateOracleRejectsCatchAllStatus(t *testing.T) {
	previousArgs, previousBaselines := args, translateBaselines
	defer func() { args, translateBaselines = previousArgs, previousBaselines }()
	args = arguments{Retries: 0}
	translateBaselines = make(map[string]translateBaseline)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusUnauthorized, ""), nil
	})}

	_, matched, err := translateExistsAgainstBaseline(client, &httpStats{}, "http://example.test/", "srcpage.aspx", "", ".aspx")
	if err != nil {
		t.Fatal(err)
	}
	if matched {
		t.Fatal("catch-all Translate status was promoted")
	}
}

func TestTranslateOracleRejectsUnstableCandidate(t *testing.T) {
	previousArgs, previousBaselines := args, translateBaselines
	defer func() { args, translateBaselines = previousArgs, previousBaselines }()
	args = arguments{Retries: 0}
	translateBaselines = make(map[string]translateBaseline)
	candidateRequests := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		status := http.StatusNotFound
		if req.URL.Path == "/srcpage.aspx" {
			candidateRequests++
			if candidateRequests == 1 {
				status = http.StatusUnauthorized
			}
		}
		return responseFor(req, status, ""), nil
	})}

	_, matched, err := translateExistsAgainstBaseline(client, &httpStats{}, "http://example.test/", "srcpage.aspx", "", ".aspx")
	if err != nil {
		t.Fatal(err)
	}
	if matched {
		t.Fatal("unstable Translate candidate was promoted")
	}
}

func TestBruteForceTranslatePinsGETAndIgnoresBruteStatus(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousTranslateBaselines := translateBaselines
	previousRegex, previousBruteStatuses := checksumRegex, bruteStatuses
	previousCandidateWriter := candidateOutputWriter
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		translateBaselines = previousTranslateBaselines
		checksumRegex, bruteStatuses = previousRegex, previousBruteStatuses
		candidateOutputWriter = previousCandidateWriter
	}()
	args = arguments{
		Autocomplete: "none", Output: "human", ProbeCandidates: true, ProbeStatus: "200",
		ProbeOracle: "translate", ProbeMethod: "OPTIONS", Retries: 0,
	}
	var output bytes.Buffer
	outputWriter = &output
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	translateBaselines = make(map[string]translateBaseline)
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	bruteStatuses = map[int]struct{}{http.StatusOK: {}}
	candidateOutputWriter = nil
	wc := newWordlistConfig([]wordlistSource{{
		name: "exact",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("SrcPage.aspx\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	methods := make(map[string]int)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		methods[req.Method]++
		status := http.StatusNotFound
		if req.URL.Path == "/SrcPage.aspx" {
			status = http.StatusUnauthorized
		}
		return responseFor(req, status, ""), nil
	})}
	ac := &attackConfig{
		wordlist: wc, foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{}),
	}
	match := recoverLongName(client, &httpStats{}, ac, baseRequest{
		url: "http://example.test/", file: "SRCPAG", tilde: "~1", ext: ".ASP",
	})
	if match.path != "SrcPage.aspx" || match.status != http.StatusUnauthorized {
		t.Fatalf("Translate brute result missing: %+v", match)
	}
	if match.oracle != "translate" || match.method != http.MethodGet {
		t.Fatalf("Translate provenance missing: %+v", match)
	}
	if methods[http.MethodGet] == 0 || len(methods) != 1 {
		t.Fatalf("brute method was not pinned to GET: %#v", methods)
	}
	if !strings.Contains(output.String(), "translate/GET") || !strings.Contains(output.String(), "status 401") {
		t.Fatalf("Translate profile missing from output: %q", output.String())
	}
}
