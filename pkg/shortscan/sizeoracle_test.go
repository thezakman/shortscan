package shortscan

import (
	"net/http"
	"strings"
	"testing"
)

func TestWebDAVAdvertisedDetectsDAVHeaderOrAllow(t *testing.T) {
	davHeader := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		res := responseFor(req, 200, "ok")
		res.Header.Set("DAV", "1,2")
		return res, nil
	})}
	if !webDAVAdvertised(davHeader, &httpStats{}, "http://iis.test/") {
		t.Fatal("a DAV response header must count as WebDAV advertised")
	}

	allowPropfind := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		res := responseFor(req, 200, "ok")
		res.Header.Set("Allow", "GET, HEAD, PROPFIND, OPTIONS")
		return res, nil
	})}
	if !webDAVAdvertised(allowPropfind, &httpStats{}, "http://iis.test/") {
		t.Fatal("Allow: PROPFIND must count as WebDAV advertised")
	}

	plain := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		res := responseFor(req, 200, "ok")
		res.Header.Set("Allow", "GET, HEAD, OPTIONS")
		return res, nil
	})}
	if webDAVAdvertised(plain, &httpStats{}, "http://iis.test/") {
		t.Fatal("no DAV header and no PROPFIND in Allow must not count as advertised")
	}
}

func TestSizeOracleRequiresWebDAVAdvertised(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{TildeEncoding: "default"}

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.Method == "OPTIONS" {
			return responseFor(req, 200, "ok"), nil // no DAV header, no PROPFIND in Allow
		}
		t.Fatalf("unexpected %s request without WebDAV advertised: %s", req.Method, req.URL)
		return nil, nil
	})}
	ac := &attackConfig{}
	if calibrateSizeOracle("http://iis.test/", client, &httpStats{}, ac, []string{""}, func() bool { return false }) {
		t.Fatal("must not fire when WebDAV isn't advertised")
	}
}

// sizeOracleTransport models a WebDAV-enabled server where PROPFIND answers a
// flat 404 (status is uniform, so no status oracle exists) but the error body
// differs meaningfully for a wildcard pattern that matches the one real
// literal-tilde marker, versus the path-echoed noise shape every other
// pattern (including random noise-floor probes and the ~0 catch-all) gets.
func sizeOracleTransport(existingMarker string) roundTripFunc {
	return func(req *http.Request) (*http.Response, error) {
		if req.Method == "OPTIONS" {
			res := responseFor(req, 200, "ok")
			res.Header.Set("DAV", "1,2")
			return res, nil
		}
		if req.Method != "PROPFIND" {
			return responseFor(req, 404, "missing"), nil
		}
		p := req.URL.EscapedPath()
		if existingMarker != "" && strings.Contains(p, existingMarker) {
			return responseFor(req, 404, "<multistatus>exists-shape-marker-xyz</multistatus>"), nil
		}
		return responseFor(req, 404, "Not Found: "+p), nil // path-echo noise
	}
}

func TestSizeOracleFindsBodyDifferential(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{TildeEncoding: "default"}

	client := &http.Client{Transport: sizeOracleTransport("~2")}
	ac := &attackConfig{}
	ok := calibrateSizeOracle("http://iis.test/", client, &httpStats{}, ac, []string{""}, func() bool { return false })
	if !ok {
		t.Fatal("expected the size oracle to find the ~2 differential")
	}
	if ac.method != "PROPFIND" {
		t.Fatalf("want method PROPFIND, got %q", ac.method)
	}
	found := false
	for _, td := range ac.tildes {
		if td == "~2" {
			found = true
		}
	}
	if !found {
		t.Fatalf("expected ~2 in ac.tildes, got %v", ac.tildes)
	}
}

func TestSizeOracleRejectsZeroCatchAll(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{TildeEncoding: "default"}

	// Every tilde digit (including ~0, which can never exist) shows the same
	// "exists" body shape — a catch-all, not a real per-name signal.
	client := &http.Client{Transport: sizeOracleTransport("~")}
	ac := &attackConfig{}
	if calibrateSizeOracle("http://iis.test/", client, &httpStats{}, ac, []string{""}, func() bool { return false }) {
		t.Fatalf("a ~0-matching catch-all must not be accepted, got tildes=%v", ac.tildes)
	}
}

func TestSizeOracleRequiresReproducibleDifferential(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{TildeEncoding: "default"}

	callsFor2 := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.Method == "OPTIONS" {
			res := responseFor(req, 200, "ok")
			res.Header.Set("DAV", "1,2")
			return res, nil
		}
		if req.Method != "PROPFIND" {
			return responseFor(req, 404, "missing"), nil
		}
		p := req.URL.EscapedPath()
		if strings.Contains(p, "~2") {
			callsFor2++
			if callsFor2 == 1 {
				return responseFor(req, 404, "<multistatus>exists-shape-marker-xyz</multistatus>"), nil
			}
			return responseFor(req, 404, "Not Found: "+p), nil // reverts to noise shape on repeat
		}
		return responseFor(req, 404, "Not Found: "+p), nil
	})}
	ac := &attackConfig{}
	if calibrateSizeOracle("http://iis.test/", client, &httpStats{}, ac, []string{""}, func() bool { return false }) {
		t.Fatalf("a one-off, non-reproducing differential must not be accepted, got tildes=%v", ac.tildes)
	}
}
