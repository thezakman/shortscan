package shortscan

import (
	"bytes"
	"net/http"
	"strings"
	"testing"
)

// altOracleTransport models a hardened front end: it mutes the common verbs the
// primary matrix uses (GET/POST/OPTIONS/HEAD/TRACE/DEBUG/PUT/PATCH/DELETE all
// answer a flat 404, so no status differential exists) while a chosen WebDAV verb
// still reaches IIS's 8.3 existence check and answers 200 for a real short name.
// hasZero keeps the ~0 catch-all guard honest: ~0 answers like the negative.
func altOracleTransport(webdavVerb string, positive int) roundTripFunc {
	return func(req *http.Request) (*http.Response, error) {
		if req.Method != webdavVerb {
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
		p := strings.ToLower(req.URL.EscapedPath())
		hasTilde := strings.Contains(p, "~") || strings.Contains(p, "%7e")
		hasZero := strings.Contains(p, "~0") || strings.Contains(p, "%7e0")
		if hasTilde && !hasZero {
			return responseFor(req, positive, "propfind hit"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	}
}

// TestAltOracleSucceedsViaWebDAVVerb is the core proof: when only a WebDAV verb
// distinguishes existing from missing short names, calibrateAltStatusOracle finds
// the oracle on that verb and records the differential.
func TestAltOracleSucceedsViaWebDAVVerb(t *testing.T) {
	client := &http.Client{Transport: altOracleTransport("PROPFIND", http.StatusOK)}
	ac := &attackConfig{}
	mk := &markers{}
	ok := calibrateAltStatusOracle("http://hardened.test/", client, &httpStats{}, ac, mk,
		[]string{"PROPFIND", "SEARCH", "MKCOL"}, []string{"/", ""}, func() bool { return false })
	if !ok {
		t.Fatal("expected alt-oracle to succeed via the WebDAV verb")
	}
	if ac.method != "PROPFIND" {
		t.Fatalf("want method PROPFIND, got %q", ac.method)
	}
	if len(ac.tildes) == 0 {
		t.Fatal("expected ac.tildes populated on success")
	}
	if mk.statusPos != http.StatusOK || mk.statusNeg != http.StatusNotFound {
		t.Fatalf("markers: pos=%d neg=%d, want 200/404", mk.statusPos, mk.statusNeg)
	}
}

// TestAltOracleNoDifferentialReturnsFalse guards against fabricating an oracle:
// a server that answers every verb identically has no 8.3 signal to offer.
func TestAltOracleNoDifferentialReturnsFalse(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	ac := &attackConfig{}
	mk := &markers{}
	if calibrateAltStatusOracle("http://flat.test/", client, &httpStats{}, ac, mk,
		[]string{"PROPFIND", "SEARCH"}, []string{"/", ""}, func() bool { return false }) {
		t.Fatal("no differential must not fabricate an oracle")
	}
	if len(ac.tildes) != 0 {
		t.Fatalf("ac.tildes must stay empty, got %v", ac.tildes)
	}
}

// TestAltOracleRejectsCatchAll locks in the ~0 guard on the alt path: a verb that
// answers 200 for EVERY tilde (including the impossible ~0) is a catch-all, not an
// oracle, and must be rejected exactly as the primary matrix rejects it.
func TestAltOracleRejectsCatchAll(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.Method != "PROPFIND" {
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
		p := strings.ToLower(req.URL.EscapedPath())
		if strings.Contains(p, "~") || strings.Contains(p, "%7e") {
			return responseFor(req, http.StatusOK, "everything is 200"), nil // ~0 too
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	ac := &attackConfig{}
	mk := &markers{}
	if calibrateAltStatusOracle("http://catchall.test/", client, &httpStats{}, ac, mk,
		[]string{"PROPFIND"}, []string{"/"}, func() bool { return false }) {
		t.Fatal("a ~0-matching catch-all must not be accepted as an oracle")
	}
}

// TestAltOracleRejectsTransientPositive ensures a 5xx/429 on the positive side is
// treated as a flapping backend, never a short-name hit (the GCLB/Cloud Armor bug
// class, on the alt path).
func TestAltOracleRejectsTransientPositive(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.Method != "PROPFIND" {
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
		p := strings.ToLower(req.URL.EscapedPath())
		hasZero := strings.Contains(p, "~0") || strings.Contains(p, "%7e0")
		hasTilde := strings.Contains(p, "~") || strings.Contains(p, "%7e")
		if hasTilde && !hasZero {
			return responseFor(req, http.StatusServiceUnavailable, "flap"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	ac := &attackConfig{}
	mk := &markers{}
	if calibrateAltStatusOracle("http://flap.test/", client, &httpStats{}, ac, mk,
		[]string{"PROPFIND"}, []string{"/"}, func() bool { return false }) {
		t.Fatal("a transient 503 positive must not anchor the oracle")
	}
}

// TestAltOracleRespectsTimeout confirms the --maxtime closure short-circuits the
// alt sweep (the reason it is threaded in rather than referenced as a global).
func TestAltOracleRespectsTimeout(t *testing.T) {
	calls := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		calls++
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	ac := &attackConfig{}
	mk := &markers{}
	if calibrateAltStatusOracle("http://slow.test/", client, &httpStats{}, ac, mk,
		[]string{"PROPFIND", "SEARCH"}, []string{"/", ""}, func() bool { return true }) {
		t.Fatal("timed-out sweep must not report an oracle")
	}
	if calls != 0 {
		t.Fatalf("timed-out sweep must send zero probes, sent %d", calls)
	}
}

// TestOracleNoteSurfacesWebDAVVerb locks in the header hint: when detection came
// from a WebDAV verb (the alt-oracle case, or the primary at patience 1), the
// Vulnerable: line names it so the operator knows the common verbs were muted.
func TestOracleNoteSurfacesWebDAVVerb(t *testing.T) {
	prev := args
	defer func() { args = prev }()
	args = arguments{Autocomplete: "method"}

	if got := oracleNote(args.Autocomplete, "PROPPATCH", ""); !strings.Contains(got, "via PROPPATCH") {
		t.Fatalf("WebDAV verb should be surfaced, got %q", got)
	}
	if got := oracleNote(args.Autocomplete, "GET", ""); strings.Contains(got, "via") {
		t.Fatalf("a common verb must not add a via-note, got %q", got)
	}
	args.Autocomplete = "none"
	if got := oracleNote(args.Autocomplete, "PROPPATCH", ""); got != "" {
		t.Fatalf("a disabled oracle must produce no note, got %q", got)
	}
}

// TestAltOracleGatedBehindAuto is the integration proof for the caller-side gate:
// the very same hardened front end yields NO oracle on a plain scan (the alt
// fallback never fires) and a detected one under --auto.
func TestAltOracleGatedBehindAuto(t *testing.T) {
	run := func(auto bool) string {
		previousArgs, previousWriter := args, outputWriter
		previousStatusCache, previousDistanceCache := statusCache, distanceCache
		defer func() {
			args, outputWriter = previousArgs, previousWriter
			statusCache, distanceCache = previousStatusCache, previousDistanceCache
		}()
		args = arguments{
			Autocomplete: "status", Output: "human", Patience: 0, Characters: "AB",
			Concurrency: 1, Retries: 0, RetryDelay: 1, TildeEncoding: "default",
			Auto: auto,
		}
		var out bytes.Buffer
		outputWriter = &out
		statusCache = make(map[string]map[int]struct{})
		distanceCache = make(map[string]map[int]distances)
		// Detection differential on PROPFIND only; every char-discovery probe still
		// answers 404 so the run detects "Vulnerable: Yes" with zero enumerated names
		// (we assert on detection, not enumeration).
		client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
			if req.Method == "PROPFIND" {
				p := strings.ToLower(req.URL.EscapedPath())
				hasZero := strings.Contains(p, "~0") || strings.Contains(p, "%7e0")
				hasTilde := strings.Contains(p, "~") || strings.Contains(p, "%7e")
				// Only the bare detection probe (/*~i*...) flips; char probes carry a
				// leading stem char and stay 404 so enumeration finds nothing.
				if hasTilde && !hasZero && strings.HasPrefix(p, "/*~") {
					return responseFor(req, http.StatusOK, "propfind hit"), nil
				}
			}
			return responseFor(req, http.StatusNotFound, "missing"), nil
		})}
		Scan([]string{"http://hardened.test/"}, client, &httpStats{}, newWordlistConfig(nil), markers{}, make(map[string]struct{}))
		return out.String()
	}

	plain := run(false)
	if strings.Contains(plain, "Vulnerable: Yes") {
		t.Fatalf("without --auto the alt-oracle must not fire, got:\n%s", plain)
	}

	auto := run(true)
	if !strings.Contains(auto, "Vulnerable: Yes") {
		t.Fatalf("under --auto the alt-oracle should detect via PROPFIND, got:\n%s", auto)
	}
	// Detection came from a WebDAV verb while recovery stays on the GET-based
	// autocomplete oracle, so the run must warn that recovery may be degraded and
	// point at the PROPFIND-based -a allow-copy workaround.
	if !strings.Contains(auto, "allow-copy") || !strings.Contains(auto, "detection used PROPFIND") {
		t.Fatalf("expected the recovery-degradation warning after WebDAV detection, got:\n%s", auto)
	}
}

// TestIsWebDAVDetectionVerb pins the verb set the alt-oracle escalates to (and
// that the degradation warning keys on).
func TestIsWebDAVDetectionVerb(t *testing.T) {
	for _, v := range []string{"PROPFIND", "SEARCH", "PROPPATCH", "MKCOL", "LOCK"} {
		if !isWebDAVDetectionVerb(v) {
			t.Errorf("%s should be a WebDAV detection verb", v)
		}
	}
	for _, v := range []string{"GET", "OPTIONS", "HEAD", "POST", "DELETE", ""} {
		if isWebDAVDetectionVerb(v) {
			t.Errorf("%s must NOT be a WebDAV detection verb (the primary matrix covers it)", v)
		}
	}
}
