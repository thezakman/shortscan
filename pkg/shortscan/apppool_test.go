package shortscan

import (
	"bytes"
	"net/http"
	"strings"
	"testing"
)

// realResource is the target the probe was pointed at; a non-existent sibling
// (random name) must answer 404 so the probe can prove a form resolves the real
// resource rather than blanket-answering.
const realResource = "/read.aspx"

// vulnerableApppoolClient models the H24 signature: native-recognised cookieless
// forms are blocked (403.18) across the app boundary, while managed-only forms
// execute the real resource (200) but 404 on a non-existent sibling.
func vulnerableApppoolClient() *http.Client {
	managed := []string{"/(%53(X))/", "/(S(X)%29/", "/%28S(X))/", "/(S(%58))/"}
	canonical := []string{"/(S(X))/", "/%28S(X)%29/"}
	control := "/(s(X))/"
	return &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		esc := req.URL.EscapedPath()
		real := strings.HasSuffix(esc, realResource)
		for _, m := range managed {
			if strings.HasPrefix(esc, m) {
				if real {
					return responseFor(req, http.StatusOK, "child-body"), nil
				}
				return responseFor(req, http.StatusNotFound, "missing"), nil
			}
		}
		for _, c := range canonical {
			if strings.HasPrefix(esc, c) {
				return responseFor(req, http.StatusForbidden, "403.18"), nil
			}
		}
		if strings.HasPrefix(esc, control) {
			return responseFor(req, http.StatusNotFound, "missing"), nil
		}
		// baseline
		if real {
			return responseFor(req, http.StatusOK, "child-body"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
}

func TestApppoolProbeFlagsBypass(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", Retries: 0}

	probeBypassURLs([]string{"http://example.test/child/read.aspx"}, vulnerableApppoolClient(), &httpStats{})
	s := out.String()
	// App-pool crossing is medium confidence in the unified probe: the baseline
	// already executes, so the resource-access is not itself denied — the crossed
	// pool/identity still needs an APP_POOL_ID echo to confirm.
	if !strings.Contains(s, "[candidate/medium]") {
		t.Fatalf("expected a medium-confidence app-pool candidate; output=%q", s)
	}
	if !strings.Contains(s, "app-pool isolation bypass (H24)") {
		t.Fatalf("output missing the H24 classification: %q", s)
	}
	if !strings.Contains(s, "managed-only:tag") {
		t.Fatalf("output missing the managed-only bypass form: %q", s)
	}
}

func TestApppoolProbeNegativeWhenControlAlsoExecutes(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", Retries: 0}

	// A server that runs EVERY parenthesised segment (including the invalid
	// lowercase-tag control) is a false positive that must be rejected.
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if strings.HasSuffix(req.URL.EscapedPath(), realResource) {
			return responseFor(req, http.StatusOK, "ok"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	probeBypassURLs([]string{"http://example.test/child/read.aspx"}, client, &httpStats{})
	if s := out.String(); !strings.Contains(s, "[negative]") {
		t.Fatalf("expected negative when the invalid control also executes; output=%q", s)
	}
}
