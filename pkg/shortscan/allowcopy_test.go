package shortscan

import (
	"bytes"
	"io"
	"net/http"
	"regexp"
	"strings"
	"testing"
)

func allowResponse(req *http.Request, includeCopy bool) *http.Response {
	res := responseFor(req, http.StatusMethodNotAllowed, "same 405 body")
	allow := "GET, HEAD, OPTIONS, TRACE, LOCK, UNLOCK"
	if includeCopy {
		allow += ", COPY"
	}
	res.Header.Set("Allow", allow)
	return res
}

func TestAllowCopyOracleUsesReadOnlyDepthZeroAndStableControls(t *testing.T) {
	previousArgs, previousBaselines := args, allowCopyBaselines
	defer func() { args, allowCopyBaselines = previousArgs, previousBaselines }()
	args = arguments{Retries: 0}
	allowCopyBaselines = make(map[string]allowCopyBaseline)

	methods := make(map[string]int)
	paths := make(map[string]int)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		methods[req.Method]++
		paths[req.URL.Path]++
		if req.Method != "PROPFIND" {
			t.Fatalf("oracle sent mutating/unexpected method %q", req.Method)
		}
		if req.Header.Get("Depth") != "0" || req.Header.Get("Cache-Control") != "no-cache" {
			t.Fatalf("missing oracle headers: %#v", req.Header)
		}
		return allowResponse(req, req.URL.Path == "/PagedList.dll"), nil
	})}

	res, matched, err := allowCopyExistsAgainstBaseline(client, &httpStats{}, "http://example.test/", "PagedList.dll", "", ".dll")
	if err != nil {
		t.Fatal(err)
	}
	if !matched || res.StatusCode != http.StatusMethodNotAllowed {
		t.Fatalf("stable Allow/COPY differential not accepted: matched=%v status=%d", matched, res.StatusCode)
	}
	if methods["PROPFIND"] != 6 || len(methods) != 1 {
		t.Fatalf("unexpected request lattice: %#v", methods)
	}
	if paths["/PagedList.dll"] != 2 {
		t.Fatalf("candidate was not repeated: %#v", paths)
	}
}

func TestAllowCopyOracleRejectsCatchAllCopyAdvertisement(t *testing.T) {
	previousArgs, previousBaselines := args, allowCopyBaselines
	defer func() { args, allowCopyBaselines = previousArgs, previousBaselines }()
	args = arguments{Retries: 0}
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return allowResponse(req, true), nil
	})}

	_, matched, err := allowCopyExistsAgainstBaseline(client, &httpStats{}, "http://example.test/", "PagedList.dll", "", ".dll")
	if err != nil {
		t.Fatal(err)
	}
	if matched {
		t.Fatal("catch-all COPY advertisement was promoted as file existence")
	}
}

func TestAllowCopyOracleRequiresCopyToBeTheOnlyCapabilityDifference(t *testing.T) {
	previousArgs, previousBaselines := args, allowCopyBaselines
	defer func() { args, allowCopyBaselines = previousArgs, previousBaselines }()
	args = arguments{Retries: 0}
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		res := allowResponse(req, req.URL.Path == "/PagedList.dll")
		if req.URL.Path == "/PagedList.dll" {
			res.Header.Add("Allow", "DELETE")
		}
		return res, nil
	})}

	_, matched, err := allowCopyExistsAgainstBaseline(client, &httpStats{}, "http://example.test/", "PagedList.dll", "", ".dll")
	if err != nil {
		t.Fatal(err)
	}
	if matched {
		t.Fatal("candidate with an extra capability beyond COPY was promoted")
	}
}

func TestAllowCopyOracleRejectsUnstableControl(t *testing.T) {
	previousArgs, previousBaselines := args, allowCopyBaselines
	defer func() { args, allowCopyBaselines = previousArgs, previousBaselines }()
	args = arguments{Retries: 0}
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	requestsByPath := make(map[string]int)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requestsByPath[req.URL.Path]++
		res := allowResponse(req, req.URL.Path == "/PagedList.dll")
		if req.URL.Path != "/PagedList.dll" && requestsByPath[req.URL.Path] > 1 {
			res.Header.Add("Allow", "POST")
		}
		return res, nil
	})}

	_, matched, err := allowCopyExistsAgainstBaseline(client, &httpStats{}, "http://example.test/", "PagedList.dll", "", ".dll")
	if err != nil {
		t.Fatal(err)
	}
	if matched {
		t.Fatal("candidate was promoted after a control capability changed")
	}
}

func TestAllowCopyOracleRejectsUnstableCandidate(t *testing.T) {
	previousArgs, previousBaselines := args, allowCopyBaselines
	defer func() { args, allowCopyBaselines = previousArgs, previousBaselines }()
	args = arguments{Retries: 0}
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	candidateRequests := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		includeCopy := false
		if req.URL.Path == "/PagedList.dll" {
			candidateRequests++
			includeCopy = candidateRequests == 1
		}
		return allowResponse(req, includeCopy), nil
	})}

	_, matched, err := allowCopyExistsAgainstBaseline(client, &httpStats{}, "http://example.test/", "PagedList.dll", "", ".dll")
	if err != nil {
		t.Fatal(err)
	}
	if matched {
		t.Fatal("unstable candidate capability was promoted")
	}
}

func TestAllowCopyOracleCarriesNamedStreamSuffixToCandidateAndControls(t *testing.T) {
	previousArgs, previousBaselines := args, allowCopyBaselines
	defer func() { args, allowCopyBaselines = previousArgs, previousBaselines }()
	args = arguments{Retries: 0}
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	const suffix = ":Zone.Identifier:$DATA"
	controlCount := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if !strings.HasSuffix(req.URL.Path, suffix) {
			t.Fatalf("named-stream suffix missing from %q", req.URL.Path)
		}
		if req.URL.Path != "/PagedList.dll"+suffix {
			controlCount++
			stem := strings.TrimSuffix(strings.TrimPrefix(req.URL.Path, "/"), ".dll"+suffix)
			if len(stem) != len("PagedList") {
				t.Fatalf("control did not preserve candidate stem length: %q", req.URL.Path)
			}
		}
		return allowResponse(req, req.URL.Path == "/PagedList.dll"+suffix), nil
	})}

	_, matched, err := allowCopyExistsAgainstBaseline(client, &httpStats{}, "http://example.test/", "PagedList.dll", suffix, ".dll")
	if err != nil {
		t.Fatal(err)
	}
	if !matched || controlCount != 4 {
		t.Fatalf("named-stream capability was not confirmed: matched=%v controls=%d", matched, controlCount)
	}
}

func TestBruteForceAllowCopyIgnoresSameStatusFilterAndPinsPropfind(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousAllowCopyBaselines := allowCopyBaselines
	previousRegex, previousBruteStatuses := checksumRegex, bruteStatuses
	previousCandidateWriter := candidateOutputWriter
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		allowCopyBaselines = previousAllowCopyBaselines
		checksumRegex, bruteStatuses = previousRegex, previousBruteStatuses
		candidateOutputWriter = previousCandidateWriter
	}()
	args = arguments{
		Autocomplete: "none", Output: "human", ProbeCandidates: true, ProbeStatus: "200",
		ProbeOracle: "allow-copy", ProbeMethod: "GET", Retries: 0,
	}
	var output bytes.Buffer
	outputWriter = &output
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	bruteStatuses = map[int]struct{}{http.StatusOK: {}}
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
	methods := make(map[string]int)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		methods[req.Method]++
		return allowResponse(req, req.URL.Path == "/PagedList.dll"), nil
	})}
	ac := &attackConfig{
		wordlist: wc, foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{}),
	}
	match := recoverLongName(client, &httpStats{}, ac, baseRequest{
		url: "http://example.test/", file: "PAGEDL", tilde: "~1", ext: ".DLL",
	})
	if match.path != "PagedList.dll" || match.status != http.StatusMethodNotAllowed {
		t.Fatalf("Allow/COPY brute result missing: %+v", match)
	}
	if match.oracle != "allow-copy" || match.method != "PROPFIND" {
		t.Fatalf("oracle provenance missing: %+v", match)
	}
	if methods["PROPFIND"] == 0 || len(methods) != 1 {
		t.Fatalf("brute-method was not safely pinned: %#v", methods)
	}
	if !strings.Contains(output.String(), "allow-copy/PROPFIND") || !strings.Contains(output.String(), "status 405") {
		t.Fatalf("oracle profile missing from output: %q", output.String())
	}
}
