package shortscan

import (
	"bytes"
	"io"
	"net/http"
	"strings"
	"testing"
)

func TestExistsLikeStatus(t *testing.T) {
	// Auth-gated / redirecting endpoints exist but never answer 405 to the method
	// probe; method-magic alone dropped them. These must count as "exists-like".
	for _, s := range []int{301, 302, 307, 308, 401, 403} {
		if !existsLikeStatus(s) {
			t.Fatalf("status %d should be exists-like (auth/redirect endpoint)", s)
		}
	}
	// Missing / error / the method-magic signal itself are NOT the fallback set.
	for _, s := range []int{200, 400, 404, 405, 500} {
		if existsLikeStatus(s) {
			t.Fatalf("status %d must not be treated as exists-like by the method fallback", s)
		}
	}
}

// In method mode, a candidate that returns 302/401 (real but protected) and whose
// non-existent sibling returns 404 must be confirmed via the status fallback.
func TestAutocompleteMethodModeConfirmsAuthGated(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Autocomplete: "method", Retries: 0}
	statusCache = make(map[string]map[int]struct{})

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		// The real protected endpoint redirects to login (302); anything else 404s.
		if strings.HasSuffix(req.URL.Path, "/XONEADMIN") {
			return responseFor(req, http.StatusFound, "redirect to login"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}

	ac := &attackConfig{autocomplete: args.Autocomplete}
	br := baseRequest{url: "http://example.test/", file: "XONEAD"}
	cand := filenameCandidate{record: wordlistRecord{filename: "XONEADMIN"}, matchType: "wordlist"}

	_, matched, err := probeAutocompleteCandidate(client, &httpStats{}, ac, br, "http://example.test/", cand)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !matched {
		t.Fatalf("method mode must confirm a 302 auth-gated endpoint via the status fallback")
	}
}

// Regression: the status shown next to a resolved long name must be the resource's
// real GET status, not the method-magic 405. Live, an openly served LIBMAN.JSON (GET
// 200) was displayed as (405) because that is the "_"-method existence signal.
func TestDisplayStatusMethodModeUsesGet(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0}

	var methods []string
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		methods = append(methods, req.Method)
		if req.Method == http.MethodGet {
			return responseFor(req, http.StatusOK, "served"), nil
		}
		return responseFor(req, http.StatusMethodNotAllowed, "method not allowed"), nil
	})}

	// method-magic mode: the 405 probe status must be overridden by the real GET (200).
	if got := displayStatus(client, &httpStats{}, args.Autocomplete, "_", "http://example.test/LIBMAN.JSON", http.StatusMethodNotAllowed); got != http.StatusOK {
		t.Fatalf("method-magic display status = %d, want 200 (real GET)", got)
	}
	if len(methods) != 1 || methods[0] != http.MethodGet {
		t.Fatalf("expected exactly one follow-up GET, got %v", methods)
	}

	// a real-method oracle keeps its probe status without an extra request.
	methods = nil
	if got := displayStatus(client, &httpStats{}, args.Autocomplete, "GET", "http://example.test/x", http.StatusFound); got != http.StatusFound {
		t.Fatalf("non-method-magic display status = %d, want 302 (probe status unchanged)", got)
	}
	if len(methods) != 0 {
		t.Fatalf("non-method-magic path must not issue an extra request, got %v", methods)
	}
}

// Reproduces a false positive observed live against a real target: a genuinely
// missing candidate (WEBSITE.PUBLISHPROJ, confirmed 404 by hand) was reported as a
// match because the default 2-probe baseline happened to miss the 404 status that
// junk paths for that unusual extension also sometimes return (an inconsistent
// server). Escalating the baseline before trusting an apparent hit must catch this.
func TestStatusModeEscalationCatchesFalsePositive(t *testing.T) {
	previousArgs := args
	previousStatusCache := statusCache
	defer func() { args = previousArgs; statusCache = previousStatusCache }()
	args = arguments{Autocomplete: "status", Retries: 0}
	statusCache = make(map[string]map[int]struct{})

	var n int
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if strings.HasSuffix(req.URL.Path, "/WEBSITE.PUBLISHPROJ") {
			return responseFor(req, http.StatusNotFound, "genuinely missing"), nil
		}
		// Junk (baseline/escalation) probes: the first 2 (the cheap default
		// baseline) return 400; from the 3rd probe on (escalation), one of them
		// reveals the server also 404s junk for this extension — an inconsistent
		// "missing" signal a 2-sample baseline can easily miss.
		n++
		if n == 3 {
			return responseFor(req, http.StatusNotFound, "junk also 404s"), nil
		}
		return responseFor(req, http.StatusBadRequest, "junk"), nil
	})}

	ac := &attackConfig{autocomplete: args.Autocomplete}
	br := baseRequest{url: "http://example.test/", file: "WEBSIT", tilde: "~1", ext: ".PUB"}
	cand := filenameCandidate{record: wordlistRecord{filename: "WEBSITE", extension: ".PUBLISHPROJ"}, matchType: "wordlist"}

	_, matched, err := probeAutocompleteCandidate(client, &httpStats{}, ac, br, "http://example.test/", cand)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if matched {
		t.Fatalf("escalated baseline should have caught the 404 the small sample missed, no false positive")
	}
	if n < 3 {
		t.Fatalf("expected escalation to run (at least 3 junk probes), only saw %d", n)
	}
}

// TestFullFallsThroughToMethodOracle is a regression guard for the --full
// resolution bug (v0.64.1): --full enables --probe-candidates, whose default
// status-oracle brute (GET, accept 200) cannot confirm a request-filtered or
// auth-gated file that only betrays itself through the method oracle (405 to an
// invalid method). The brute finding nothing must therefore FALL THROUGH to the
// method-oracle resolution, so --full resolves at least what --auto does. Before
// the fix the brute ended in an unconditional `return first`, so --full silently
// resolved FEWER names than --auto on the very same wordlist.
func TestFullFallsThroughToMethodOracle(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousBruteStatuses := bruteStatuses
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		bruteStatuses = previousBruteStatuses
	}()
	args = arguments{
		Full: true, ProbeCandidates: true, ProbeStatus: "200",
		Output: "human", Retries: 0,
	}
	var output bytes.Buffer
	outputWriter = &output
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	bruteStatuses = map[int]struct{}{http.StatusOK: {}}

	wc := newWordlistConfig([]wordlistSource{{
		name: "regress",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("secret.aspx\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}

	// secret.aspx exists but is auth-gated: GET answers 404 (the brute's {200}
	// oracle rejects it), while the invalid method "_" answers 405 ("exists").
	// Every random same-extension probe answers 404 to every method (baseline).
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.Method == "_" && req.URL.Path == "/secret.aspx" {
			return responseFor(req, http.StatusMethodNotAllowed, "exists"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}

	ac := &attackConfig{
		wordlist: wc, autocomplete: "method",
		foundFiles: make(map[string]struct{}), foundDirectories: make(map[string]struct{}),
	}
	match := recoverLongName(client, &httpStats{}, ac, baseRequest{
		url: "http://example.test/", file: "SECRET", tilde: "~1", ext: ".ASP",
	})
	if match.path != "secret.aspx" {
		t.Fatalf("--full did not fall through to the method oracle after an empty brute: got %+v, want path=secret.aspx", match)
	}
	if _, ok := ac.foundFiles[foundFileKey("secret.aspx")]; !ok {
		t.Fatalf("resolved name not recorded in foundFiles: %v", ac.foundFiles)
	}
}

// TestTestIndexAllocationsNoLongerGuessesBinOnBareRoot locks in the fix for a live
// "wtf?"/"revisa" moment: standalone `-i` (no --auto/--full) pointed at a bare site
// root silently substituted "/bin" behind the user's back before probing
// ::$INDEX_ALLOCATION — confusing (the printed URL never matched what was typed) and
// wrong whenever the real target was a different reserved folder. `name::$INDEX_
// ALLOCATION` needs a NAMED directory segment to suffix, which a bare root doesn't
// have, so -i now prints a clear explanation and sends ZERO requests for a root
// target instead of guessing. A named target (…/bin) is completely unaffected —
// still probed exactly as given, no behavior change there.
func TestTestIndexAllocationsNoLongerGuessesBinOnBareRoot(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	args = arguments{Output: "human", Retries: 0}
	var out bytes.Buffer
	outputWriter = &out

	requested := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requested++
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}

	testIndexAllocations([]string{"https://h.test/"}, client, &httpStats{}, newWordlistConfig(nil), markers{})

	if requested != 0 {
		t.Fatalf("a bare root must send ZERO requests (no more silent /bin guess), got %d", requested)
	}
	if !strings.Contains(out.String(), "bare site root") {
		t.Fatalf("expected the bare-root explanation in output, got %q", out.String())
	}
	if strings.Contains(out.String(), "/bin::$INDEX_ALLOCATION") {
		t.Fatalf("must NOT silently probe /bin for a bare root, output was %q", out.String())
	}

	// A named target is unaffected: still probed exactly as given.
	out.Reset()
	requested = 0
	var sawBinURL bool
	client2 := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requested++
		if strings.Contains(req.URL.String(), "/bin::$INDEX_ALLOCATION") {
			sawBinURL = true
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	testIndexAllocations([]string{"https://h.test/bin"}, client2, &httpStats{}, newWordlistConfig(nil), markers{})
	if requested == 0 || !sawBinURL {
		t.Fatalf("a named /bin target must still be probed as given, requested=%d sawBinURL=%v", requested, sawBinURL)
	}
}
