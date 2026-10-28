package shortscan

import (
	"net/http"
	"path"
	"strings"
	"sync"
	"testing"
)

func runProfileEnumeration(t *testing.T, profiles []oracleProfile, rt roundTripFunc) []enumEntry {
	t.Helper()
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Output: "human", Concurrency: 2, Retries: 0, Autocomplete: "none"}
	client := &http.Client{Transport: rt}
	ac := &attackConfig{autocomplete: "none", oracleProfiles: profiles}
	sem := make(chan struct{}, args.Concurrency)
	for i := range ac.oracleProfiles {
		wg := new(sync.WaitGroup)
		enumerate(sem, wg, client, &httpStats{}, ac, &ac.oracleProfiles[i], baseRequest{url: "http://example.test/", tilde: "~1"})
		wg.Wait()
	}
	return ac.enumEntries
}

func testProfile(method string, positive int) oracleProfile {
	return oracleProfile{
		method: method, detectionOracle: "status", tildes: []string{"~1"},
		markersByTilde: map[string]markers{"~1": {statusPos: positive, statusNeg: http.StatusOK}},
		fileChars:      map[string]string{"~1": "A"},
		extChars:       map[string]string{"~1": ""},
	}
}

func TestInstallBatchOracleProfilesRetainsDisjointMethods(t *testing.T) {
	ac := &attackConfig{}
	mk := markers{}
	results := []matrixProbeResult{
		{
			method: "OPTIONS", suffix: "/", statusNeg: 200, statusPos: 404,
			tildes:         []string{"~1"},
			markersByTilde: map[string]markers{"~1": {statusPos: 404, statusNeg: 200}},
		},
		{
			method: "HEAD", suffix: "/", statusNeg: 200, statusPos: 404,
			tildes:         []string{"~2"},
			markersByTilde: map[string]markers{"~2": {statusPos: 404, statusNeg: 200}},
		},
	}
	if !installBatchOracleProfiles(ac, &mk, results) {
		t.Fatal("stable batch was not installed")
	}
	if len(ac.oracleProfiles) != 2 {
		t.Fatalf("profiles=%d, want 2", len(ac.oracleProfiles))
	}
	if ac.oracleProfiles[0].method != "OPTIONS" || ac.oracleProfiles[1].method != "HEAD" {
		t.Fatalf("profile order/methods changed: %+v", ac.oracleProfiles)
	}
	if got := len(ac.profilesForTilde("~1")); got != 1 {
		t.Fatalf("~1 profiles=%d, want 1", got)
	}
	if got := len(ac.profilesForTilde("~2")); got != 1 {
		t.Fatalf("~2 profiles=%d, want 1", got)
	}
}

func TestLaterPortfolioWindowDoesNotReplacePrimaryProfile(t *testing.T) {
	ac := &attackConfig{}
	mk := markers{}
	first := []matrixProbeResult{{
		method: "OPTIONS", suffix: "/", tildes: []string{"~1"},
		markersByTilde: map[string]markers{"~1": {statusPos: 404, statusNeg: 200}},
	}}
	later := []matrixProbeResult{{
		method: "PROPFIND", suffix: "/.aspx", tildes: []string{"~2"},
		markersByTilde: map[string]markers{"~2": {statusPos: 403, statusNeg: 200}},
	}}
	installBatchOracleProfiles(ac, &mk, first)
	installBatchOracleProfiles(ac, &mk, later)
	if len(ac.oracleProfiles) != 2 {
		t.Fatalf("profiles=%d, want 2", len(ac.oracleProfiles))
	}
	if ac.method != "OPTIONS" || ac.suffix != "/" || mk.statusPos != 404 {
		t.Fatalf("later window replaced primary: method=%q suffix=%q markers=%+v", ac.method, ac.suffix, mk)
	}
}

func TestProbeOracleURLKeepsTypedProfilesSeparate(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 0}
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.Method == "OPTIONS" {
			return responseFor(req, http.StatusNotFound, "options"), nil
		}
		return responseFor(req, http.StatusForbidden, "head"), nil
	})}
	ac := &attackConfig{oracleProfiles: []oracleProfile{
		{
			method: "OPTIONS", suffix: "/", detectionOracle: "status", tildes: []string{"~1"},
			markersByTilde: map[string]markers{"~1": {statusPos: 404, statusNeg: 200}},
		},
		{
			method: "HEAD", suffix: "/", detectionOracle: "status", tildes: []string{"~2"},
			markersByTilde: map[string]markers{"~2": {statusPos: 403, statusNeg: 200}},
		},
	}}

	res, profile, matched, err := probeOracleURL(client, &httpStats{}, ac, "~1", "http://example.test/ALPHAA~1.TXT")
	if err != nil || !matched || res.StatusCode != 404 || profile.method != "OPTIONS" {
		t.Fatalf("~1 match wrong: status=%v profile=%+v matched=%v err=%v", res, profile, matched, err)
	}
	res, profile, matched, err = probeOracleURL(client, &httpStats{}, ac, "~2", "http://example.test/BETAAA~2.ASP")
	if err != nil || !matched || res.StatusCode != 403 || profile.method != "HEAD" {
		t.Fatalf("~2 match wrong: status=%v profile=%+v matched=%v err=%v", res, profile, matched, err)
	}
}

func TestProbeOracleURLDoesNotCrossAcceptStatus(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusForbidden, "wrong profile"), nil
	})}
	ac := &attackConfig{oracleProfiles: []oracleProfile{{
		method: "OPTIONS", tildes: []string{"~1"},
		markersByTilde: map[string]markers{"~1": {statusPos: 404, statusNeg: 200}},
	}}}
	_, _, matched, err := probeOracleURL(client, &httpStats{}, ac, "~1", "http://example.test/A~1.TXT")
	if err != nil {
		t.Fatal(err)
	}
	if matched {
		t.Fatal("~1/404 profile cross-accepted a 403 response")
	}
}

func TestEnumerateDoesNotComposeDifferentProfiles(t *testing.T) {
	entries := runProfileEnumeration(t, []oracleProfile{
		testProfile("OPTIONS", http.StatusNotFound),
		testProfile("HEAD", http.StatusForbidden),
	}, roundTripFunc(func(req *http.Request) (*http.Response, error) {
		path := req.URL.Path
		if req.Method == "OPTIONS" && strings.HasSuffix(path, "/A*~1*") {
			return responseFor(req, http.StatusNotFound, "options-prefix"), nil
		}
		if req.Method == "HEAD" && (strings.HasSuffix(path, "/A~1*") || strings.HasSuffix(path, "/A~1")) {
			return responseFor(req, http.StatusForbidden, "head-tail"), nil
		}
		return responseFor(req, http.StatusOK, "negative"), nil
	}))
	if len(entries) != 0 {
		t.Fatalf("different profiles composed a Frankenstein alias: %#v", entries)
	}
}

func TestEnumerateAcceptsTerminalNonNegativeWithinProfile(t *testing.T) {
	entries := runProfileEnumeration(t, []oracleProfile{
		testProfile("OPTIONS", http.StatusNotFound),
	}, roundTripFunc(func(req *http.Request) (*http.Response, error) {
		switch {
		case strings.HasSuffix(req.URL.Path, "/A*~1*"), strings.HasSuffix(req.URL.Path, "/A~1*"):
			return responseFor(req, http.StatusNotFound, "wildcard-positive"), nil
		case strings.HasSuffix(req.URL.Path, "/A~1"):
			return responseFor(req, http.StatusForbidden, "third-terminal-class"), nil
		default:
			return responseFor(req, http.StatusOK, "negative"), nil
		}
	}))
	if len(entries) != 1 || entries[0].sortKey != "A~1" {
		t.Fatalf("terminal third status should confirm exactly one alias: %#v", entries)
	}
}

func TestEnumerateContinuesBoundProfileAcrossMultipleCharacters(t *testing.T) {
	entries := runProfileEnumeration(t, []oracleProfile{
		testProfile("OPTIONS", http.StatusNotFound),
	}, roundTripFunc(func(req *http.Request) (*http.Response, error) {
		pattern := strings.Trim(req.URL.Path, "/")
		if pattern == "AA~1" {
			return responseFor(req, http.StatusForbidden, "third-terminal-class"), nil
		}
		matched, _ := path.Match(strings.ToUpper(pattern), "AA~1")
		if matched {
			return responseFor(req, http.StatusNotFound, "wildcard-positive"), nil
		}
		return responseFor(req, http.StatusOK, "negative"), nil
	}))
	if len(entries) != 1 || entries[0].sortKey != "AA~1" {
		t.Fatalf("multi-character walk stopped before the full stem: %#v", entries)
	}
}

func TestPortfolioEmitsAliasOnlyOnceAcrossProfiles(t *testing.T) {
	entries := runProfileEnumeration(t, []oracleProfile{
		testProfile("OPTIONS", http.StatusNotFound),
		testProfile("HEAD", http.StatusForbidden),
	}, roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if strings.HasSuffix(req.URL.Path, "/A*~1*") || strings.HasSuffix(req.URL.Path, "/A~1*") || strings.HasSuffix(req.URL.Path, "/A~1") {
			if req.Method == "HEAD" {
				return responseFor(req, http.StatusForbidden, "head-positive"), nil
			}
			return responseFor(req, http.StatusNotFound, "options-positive"), nil
		}
		return responseFor(req, http.StatusOK, "negative"), nil
	}))
	if len(entries) != 1 || entries[0].sortKey != "A~1" {
		t.Fatalf("same alias should be emitted once across profiles: %#v", entries)
	}
}

func TestBodyDistanceNeverBecomesEnumerableFromMarkers(t *testing.T) {
	ac := &attackConfig{
		method: "PROPFIND", suffix: "/", detectionOracle: "body-distance", tildes: []string{"~1"},
	}
	ensureLegacyOracleProfile(ac, markers{statusPos: http.StatusNotFound, statusNeg: http.StatusOK})
	if len(ac.oracleProfiles) != 0 {
		t.Fatalf("body-distance inherited an enumerable status profile: %#v", ac.oracleProfiles)
	}
}
