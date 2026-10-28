package shortscan

import (
	"bytes"
	"net/http"
	"strings"
	"testing"
)

func TestIsStaticResource(t *testing.T) {
	// Static files (content disclosure if a managed-only token serves them, H37).
	for _, p := range []string{
		"/secure/backup_secret.txt", "/area/appsettings.json", "/x/data.xml",
		"/x/backup.zip", "/a/b/report.pdf", "/img/logo.PNG", "/s/style.css",
	} {
		if !isStaticResource(p) {
			t.Fatalf("%q should be a static resource", p)
		}
	}
	// Managed handlers (code execution, not content disclosure) and extensionless
	// routes must NOT be flagged as static.
	for _, p := range []string{
		"/secure/Panel.aspx", "/api/Service.asmx", "/h/Handler.ashx",
		"/s/Data.svc", "/trace.axd", "/classic/legacy.asp",
		"/mvc/route/without/extension", "/secure/", "/",
	} {
		if isStaticResource(p) {
			t.Fatalf("%q must not be flagged as a static resource", p)
		}
	}
}

func TestExecutedCleanly(t *testing.T) {
	// 2xx/3xx are unambiguous, clean execution — eligible for the green label.
	for _, s := range []int{200, 301, 302} {
		if !executedCleanly(s) {
			t.Fatalf("status %d should be clean execution", s)
		}
	}
	// A 500 still counts as "executed" for verdict purposes (apppoolExecuted), but
	// must NOT be treated as clean execution — a crash isn't proof of a bypass.
	if !apppoolExecuted(500) {
		t.Fatalf("apppoolExecuted must still treat 500 as executed for verdict logic")
	}
	if executedCleanly(500) {
		t.Fatalf("a 500 (crash) must not count as clean execution")
	}
	for _, s := range []int{403, 404} {
		if executedCleanly(s) {
			t.Fatalf("status %d must not count as clean execution", s)
		}
	}
}

// Reproduces a live false-positive-looking case: every form (including the invalid
// lowercase-tag control) 500s uniformly — e.g. the app itself is broken, not a
// bypass. The verdict must stay negative (the control executing too is the existing
// false-positive guard), and the row label must not be painted as a clean hit.
func TestBypassProbeAllFormsCrashIsNegative(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", Retries: 0}

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		esc := req.URL.EscapedPath()
		if strings.HasPrefix(esc, "/(S(X))/") || strings.HasPrefix(esc, "/%28S(X)%29/") {
			return responseFor(req, http.StatusForbidden, "403"), nil
		}
		// every other form, including managed-only and the lowercase control,
		// crashes uniformly (500) — the app is broken, not bypassed.
		return responseFor(req, http.StatusInternalServerError, "crash"), nil
	})}

	probeBypassURL("http://example.test/secure/Pool.aspx", client, &httpStats{})
	s := out.String()
	if !strings.Contains(s, "[negative]") {
		t.Fatalf("uniform 500s (including the lowercase control) must be negative; output=%q", s)
	}
	if strings.Contains(s, "[candidate") {
		t.Fatalf("must not report a candidate when every form (incl. control) crashes; output=%q", s)
	}
}

// vulnerableDirScopedSplitClient models the H58 signature (research/52): a native
// ipSecurity control scoped to a DIRECTORY (`<location path="secure">`) blocks the
// direct request AND every leading-token form (H34) — the standalone token never
// touches the "secure" segment, so the raw path still matches the location — but
// splitting "secure" itself (dir-split, token fused INSIDE the segment) desyncs the
// match and serves the real resource, 404ing a same-shape random sibling.
func vulnerableDirScopedSplitClient() *http.Client {
	return &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		esc := req.URL.EscapedPath()
		// "secure" survives intact as its own segment -> the location still matches,
		// regardless of any standalone token elsewhere in the path (leading-token sweep).
		if strings.Contains(esc, "/secure/") || strings.HasSuffix(esc, "/secure") {
			return responseFor(req, http.StatusForbidden, "403.503"), nil
		}
		// "secure" has been split -> the raw match no longer applies; the collapse
		// reforms the real path and it is served (or 404s a non-existent sibling).
		if strings.HasSuffix(esc, "/read.aspx") {
			return responseFor(req, http.StatusOK, "leaked-body"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
}

// TestBypassProbeSegmentSplitCatchesDirectoryScopedLocation is the regression test
// for the session's real finding: --bypass-probe only swept the standalone
// leading-token geometry (H34/H35), which a FILE- or DIRECTORY-scoped native
// <location> control survives (research/52, H58) — a real false negative. The probe
// must fall through to the segment-split geometry and still report a candidate.
func TestBypassProbeSegmentSplitCatchesDirectoryScopedLocation(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", Retries: 0}

	probeBypassURL("http://example.test/secure/read.aspx", vulnerableDirScopedSplitClient(), &httpStats{})
	s := out.String()
	if !strings.Contains(s, "no bypass") {
		t.Fatalf("expected the leading-token sweep to report no bypass at every position (H58 precondition); output=%q", s)
	}
	if !strings.Contains(s, "[candidate/high]") {
		t.Fatalf("expected the segment-split fallback to flag a high-confidence candidate; output=%q", s)
	}
	if !strings.Contains(s, "(H58)") {
		t.Fatalf("expected the finding to be attributed to H58 (segment-split); output=%q", s)
	}
	if !strings.Contains(s, "segment-split:dir-split") {
		t.Fatalf("expected the bypass form to name dir-split; output=%q", s)
	}
}

// TestBypassProbeSegmentSplitStaysNegativeWhenNothingDesyncs is the companion
// negative control: when NEITHER the leading-token sweep NOR the segment-split
// sweep desyncs the control (a target genuinely closed to every geometry), the
// probe must not manufacture a candidate.
func TestBypassProbeSegmentSplitStaysNegativeWhenNothingDesyncs(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human", Retries: 0}

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		// The control denies EVERY geometry, split included — nothing ever resolves
		// the real resource.
		return responseFor(req, http.StatusForbidden, "403.503"), nil
	})}

	probeBypassURL("http://example.test/secure/read.aspx", client, &httpStats{})
	s := out.String()
	if !strings.Contains(s, "[negative]") {
		t.Fatalf("expected negative when no geometry (leading-token or segment-split) desyncs the control; output=%q", s)
	}
	if !strings.Contains(s, "segment-split/H58 geometry") {
		t.Fatalf("expected the negative note to record that segment-split was also tried; output=%q", s)
	}
}
