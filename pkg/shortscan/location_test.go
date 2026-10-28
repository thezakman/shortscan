package shortscan

import (
	"bytes"
	"net/http"
	"strings"
	"testing"
)

// vulnerableLocationClient models the H34 signature: the DIRECT request is denied
// (403 — an ipSecurity/authorization guard on the <location>), canonical cookieless
// forms stay denied (stripped before the location match), while managed-only forms
// execute the guarded resource (200) yet 404 on a non-existent sibling.
func vulnerableLocationClient() *http.Client {
	managed := []string{"/(%53(X))/", "/(S(X)%29/", "/%28S(X))/", "/(S(%58))/"}
	canonical := []string{"/(S(X))/", "/%28S(X)%29/"}
	control := "/(s(X))/"
	return &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		esc := req.URL.EscapedPath()
		real := strings.HasSuffix(esc, realResource)
		for _, m := range managed {
			if strings.HasPrefix(esc, m) {
				if real {
					return responseFor(req, http.StatusOK, "secure-body"), nil
				}
				return responseFor(req, http.StatusNotFound, "missing"), nil
			}
		}
		for _, c := range canonical {
			if strings.HasPrefix(esc, c) {
				return responseFor(req, http.StatusForbidden, "403.503"), nil
			}
		}
		if strings.HasPrefix(esc, control) {
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
		// baseline: the guard denies the direct request
		return responseFor(req, http.StatusForbidden, "403.503"), nil
	})}
}

func TestLocationProbeFlagsBypass(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", Retries: 0}

	probeBypassURLs([]string{"http://example.test/secure/read.aspx"}, vulnerableLocationClient(), &httpStats{})
	s := out.String()
	if !strings.Contains(s, "[candidate/high]") {
		t.Fatalf("expected a high-confidence candidate; output=%q", s)
	}
	if !strings.Contains(s, "managed-only:tag") {
		t.Fatalf("output missing the managed-only bypass form: %q", s)
	}
}

// A 401 denied baseline is the H35 / AuthDrop signature (native authentication on a
// <location>): the probe must still flag [candidate/high] and name it H35 (not H34),
// noting the resource runs anonymously.
func TestLocationProbeNamesAuthBypassOn401(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", Retries: 0}

	managed := []string{"/(%53(X))/", "/(S(X)%29/", "/%28S(X))/", "/(S(%58))/"}
	canonical := []string{"/(S(X))/", "/%28S(X)%29/"}
	control := "/(s(X))/"
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		esc := req.URL.EscapedPath()
		real := strings.HasSuffix(esc, realResource)
		for _, m := range managed {
			if strings.HasPrefix(esc, m) {
				if real {
					return responseFor(req, http.StatusOK, "secure-body"), nil
				}
				return responseFor(req, http.StatusNotFound, "missing"), nil
			}
		}
		for _, c := range canonical {
			if strings.HasPrefix(esc, c) {
				return responseFor(req, http.StatusUnauthorized, "401.2"), nil
			}
		}
		if strings.HasPrefix(esc, control) {
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
		return responseFor(req, http.StatusUnauthorized, "401.2"), nil
	})}
	probeBypassURLs([]string{"http://example.test/winauth/read.aspx"}, client, &httpStats{})
	s := out.String()
	if !strings.Contains(s, "[candidate/high]") {
		t.Fatalf("expected a high-confidence candidate on a 401 baseline; output=%q", s)
	}
	if !strings.Contains(s, "(H35)") {
		t.Fatalf("expected the 401 auth-bypass to be named H35; output=%q", s)
	}
	if !strings.Contains(s, "ANONYMOUSLY") {
		t.Fatalf("expected the note to say the resource runs anonymously; output=%q", s)
	}
}

func TestLocationProbeNegativeWhenBaselineNotDenied(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", Retries: 0}

	// Baseline executes (200) — there is no path-scoped denial to bypass, so this
	// is the --apppool-probe shape, not a location-control bypass. Must be negative
	// even though managed-only forms "execute".
	managed := []string{"/(%53(X))/", "/(S(X)%29/", "/%28S(X))/", "/(S(%58))/"}
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		esc := req.URL.EscapedPath()
		real := strings.HasSuffix(esc, realResource)
		for _, m := range managed {
			if strings.HasPrefix(esc, m) && real {
				return responseFor(req, http.StatusOK, "ok"), nil
			}
		}
		if real {
			return responseFor(req, http.StatusOK, "ok"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	probeBypassURLs([]string{"http://example.test/secure/read.aspx"}, client, &httpStats{})
	if s := out.String(); !strings.Contains(s, "[negative]") {
		t.Fatalf("expected negative when the direct baseline is not denied; output=%q", s)
	}
}

func TestLocationProbeNegativeWhenCanonicalAlsoExecutes(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", Retries: 0}

	// Baseline denied but a canonical form ALSO executes -> the guard is not tied to
	// native cookieless removal here; reject (not the clean managed-only differential).
	control := "/(s(X))/"
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		esc := req.URL.EscapedPath()
		real := strings.HasSuffix(esc, realResource)
		if strings.HasPrefix(esc, control) {
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
		// any parenthesised form executes the real resource (incl. canonical)
		if strings.HasPrefix(esc, "/(") || strings.HasPrefix(esc, "/%28") {
			if real {
				return responseFor(req, http.StatusOK, "ok"), nil
			}
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
		return responseFor(req, http.StatusForbidden, "403.503"), nil
	})}
	probeBypassURLs([]string{"http://example.test/secure/read.aspx"}, client, &httpStats{})
	if s := out.String(); !strings.Contains(s, "[negative]") {
		t.Fatalf("expected negative when a canonical form also executes; output=%q", s)
	}
}
