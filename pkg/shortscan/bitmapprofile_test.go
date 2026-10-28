package shortscan

import (
	"bytes"
	"net/http"
	"strings"
	"testing"
)

func TestNormalizeBitmapProfileTarget(t *testing.T) {
	base, candidate, display, err := normalizeBitmapProfileTarget("https://example.test/app/LargeDirectory/")
	if err != nil {
		t.Fatal(err)
	}
	if base != "https://example.test/app/" || candidate != "LargeDirectory" || display != "https://example.test/app/LargeDirectory/" {
		t.Fatalf("unexpected normalization: base=%q candidate=%q display=%q", base, candidate, display)
	}
	for _, input := range []string{
		"https://example.test/",
		"https://example.test/app/dir?x=1",
		"https://example.test/app/dir::$BITMAP",
		"https://example.test/app/%2e%2e/",
		"ftp://example.test/app/dir/",
	} {
		if _, _, _, err := normalizeBitmapProfileTarget(input); err == nil {
			t.Errorf("invalid bitmap target %q was accepted", input)
		}
	}
}

func TestRunBitmapProfilesCSVEmitsRecord(t *testing.T) {
	previousArgs, previousWriter, previousHeader := args, outputWriter, csvHeaderPrinted
	t.Cleanup(func() {
		args, outputWriter, csvHeaderPrinted = previousArgs, previousWriter, previousHeader
	})
	args = arguments{Retries: 0, Output: "csv"}
	csvHeaderPrinted = false
	var output bytes.Buffer
	outputWriter = &output
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return bitmapProbeResponse(req, strings.Contains(req.URL.Path, "LargeDirectory")), nil
	})}
	runBitmapProfiles([]string{"https://example.test/app/LargeDirectory/"}, client, &httpStats{})
	if !strings.Contains(output.String(), "\nbitmap-profile,") || !strings.Contains(output.String(), "materialized-directory-index") {
		t.Fatalf("CSV omitted bitmap record: %q", output.String())
	}
}

func bitmapProbeResponse(req *http.Request, hasCopy bool) *http.Response {
	allow := "GET, HEAD, OPTIONS, TRACE"
	if hasCopy {
		allow += ", COPY"
	}
	res := aliasProbeTestResponse(req, http.StatusMethodNotAllowed, 0, http.NoBody)
	res.Header.Set("Allow", allow)
	return res
}

func TestProbeBitmapCapabilityClassifiesPresenceAndAbsence(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{Retries: 0}
	requests := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests++
		if req.Method != "PROPFIND" || req.Header.Get("Depth") != "0" {
			t.Errorf("unexpected request: %s depth=%q", req.Method, req.Header.Get("Depth"))
		}
		return bitmapProbeResponse(req, strings.Contains(req.URL.Path, "LargeDirectory")), nil
	})}

	present, err := probeBitmapCapability(client, &httpStats{}, "https://example.test/app/", "LargeDirectory", "::$BITMAP")
	if err != nil || !present.Available || !present.Present {
		t.Fatalf("presence observation=%+v err=%v", present, err)
	}
	absent, err := probeBitmapCapability(client, &httpStats{}, "https://example.test/app/", "SmallDirectory", "::$BITMAP")
	if err != nil || !absent.Available || absent.Present {
		t.Fatalf("absence observation=%+v err=%v", absent, err)
	}
	if requests != 12 {
		t.Fatalf("requests=%d, want 12", requests)
	}
}

func TestClassifyBitmapProfilePreservesHistoricalLimit(t *testing.T) {
	present := bitmapCapabilityObservation{Available: true, Present: true}
	absent := bitmapCapabilityObservation{Available: true, Present: false}
	classification, note, highWatermark := classifyBitmapProfile(present, present, present)
	if classification != "materialized-directory-index" || !highWatermark || !strings.Contains(note, "historical") {
		t.Fatalf("materialized classification=%q note=%q high=%t", classification, note, highWatermark)
	}
	classification, _, highWatermark = classifyBitmapProfile(present, absent, absent)
	if classification != "resident-directory-index" || highWatermark {
		t.Fatalf("resident classification=%q high=%t", classification, highWatermark)
	}
	classification, _, _ = classifyBitmapProfile(present, present, absent)
	if classification != "inconclusive" {
		t.Fatalf("disagreeing bitmap forms classified as %q", classification)
	}
}

func TestAutoBitmapTargetsAreBoundedAndIncludeReservedFolders(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{Auto: true}
	found := map[string]struct{}{"Salesforce": {}, "Documentation": {}}
	targets := autoBitmapTargets("https://example.test/app/", []string{
		"https://example.test/app/bin::$INDEX_ALLOCATION/",
		"https://example.test/app/App_Data::$INDEX_ALLOCATION/",
	}, found)
	for _, want := range []string{
		"https://example.test/app/",
		"https://example.test/app/bin/",
		"https://example.test/app/App_Data/",
		"https://example.test/app/Documentation/",
		"https://example.test/app/Salesforce/",
	} {
		seen := false
		for _, target := range targets {
			seen = seen || target == want
		}
		if !seen {
			t.Errorf("auto targets omitted %q: %#v", want, targets)
		}
	}
	if len(targets) > 6 {
		t.Fatalf("auto target budget exceeded: %d", len(targets))
	}
}

func TestAutoBitmapStopsAfterUnavailableOrigin(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	t.Cleanup(func() { args, outputWriter = previousArgs, previousWriter })
	args = arguments{Auto: true, Output: "human", Retries: 0}
	outputWriter = &bytes.Buffer{}
	requests := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests++
		return aliasProbeTestResponse(req, http.StatusNotFound, 0, http.NoBody), nil
	})}
	visited, unavailable := make(map[string]struct{}), make(map[string]struct{})
	ac := &attackConfig{foundDirectories: map[string]struct{}{"Child": {}}}
	high := runAutoBitmapProfiles(client, &httpStats{}, ac, "https://example.test/app/",
		[]string{"https://example.test/app/bin::$INDEX_ALLOCATION/"}, visited, unavailable)
	if len(high) != 0 || requests != 6 || len(unavailable) != 1 {
		t.Fatalf("high=%v requests=%d unavailable=%v", high, requests, unavailable)
	}
}

func TestAutoBitmapEmitsAndPrioritisesMaterializedDirectory(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	t.Cleanup(func() { args, outputWriter = previousArgs, previousWriter })
	args = arguments{Auto: true, Output: "human", Retries: 0}
	var output bytes.Buffer
	outputWriter = &output
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return bitmapProbeResponse(req, strings.Contains(req.URL.Path, "/app:")), nil
	})}
	visited, unavailable := make(map[string]struct{}), make(map[string]struct{})
	ac := &attackConfig{foundDirectories: make(map[string]struct{})}
	high := runAutoBitmapProfiles(client, &httpStats{}, ac, "https://example.test/app/", nil, visited, unavailable)
	if !high["https://example.test/app/"] || len(unavailable) != 0 {
		t.Fatalf("high=%v unavailable=%v", high, unavailable)
	}
	if !strings.Contains(output.String(), "[BITMAP-HIGHWATER]") || !strings.Contains(output.String(), "materialized-directory-index") {
		t.Fatalf("auto output omitted materialized profile: %q", output.String())
	}
}
