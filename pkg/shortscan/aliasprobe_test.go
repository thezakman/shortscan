package shortscan

import (
	"bytes"
	"io"
	"net/http"
	"strconv"
	"strings"
	"testing"
)

func TestParseExactShortAlias(t *testing.T) {
	tests := map[string]string{
		"pagedl~1.dll": "PAGEDL~1.DLL",
		"ABC~12":       "ABC~12",
		"A#B~1.js":     "A#B~1.JS",
		"src47.txt":    "SRC47.TXT",
		"rcfg~a.txt":   "RCFG~A.TXT",
	}
	for input, want := range tests {
		alias, err := parseExactShortAlias(input)
		if err != nil {
			t.Fatalf("parse %q: %v", input, err)
		}
		if got := alias.name(); got != want {
			t.Errorf("parse %q = %q, want %q", input, got, want)
		}
	}

	for _, input := range []string{
		"", "PAGEDLIST.DLL", "PAGEDLL~1.DLL",
		"PAGEDL~1.DLL.BAK", "PAGEDL~1.DLLL", "../PAGEDL~1.DLL", "PAGEDL~1.DLL?x=1",
		"PAGED*~1.DLL",
	} {
		if _, err := parseExactShortAlias(input); err == nil {
			t.Errorf("invalid alias %q was accepted", input)
		}
	}
}

func TestParseExactShortAliasClassifiesAutomaticAndCustomForms(t *testing.T) {
	automatic, _ := parseExactShortAlias("PAGEDL~1.DLL")
	if !automatic.Automatic || automatic.customSFNCandidate() || automatic.guardBypassCandidate() {
		t.Fatalf("automatic alias classification: %+v", automatic)
	}
	for _, input := range []string{"SRC47.TXT", "DATA47", "RCFG~A.TXT"} {
		alias, err := parseExactShortAlias(input)
		if err != nil {
			t.Fatal(err)
		}
		if alias.Automatic || !alias.customSFNCandidate() || !alias.guardBypassCandidate() {
			t.Fatalf("custom alias classification for %q: %+v", input, alias)
		}
	}
	guardedCustom, _ := parseExactShortAlias("PAGEDL~0.DLL")
	if guardedCustom.Automatic || guardedCustom.guardBypassCandidate() {
		t.Fatalf("~0 must be custom syntax but still enter the IIS tilde-digit guard: %+v", guardedCustom)
	}
}

func TestExactAliasControlsPreserveShapeAndOrdinal(t *testing.T) {
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")
	controls := exactAliasControls(alias)
	if len(controls) != 2 {
		t.Fatalf("got %d controls, want 2", len(controls))
	}
	for _, control := range controls {
		if len(control.name()) != len(alias.name()) || control.Ordinal != alias.Ordinal || control.Extension != alias.Extension {
			t.Fatalf("control changed alias shape: %q versus %q", control.name(), alias.name())
		}
		if control.name() == alias.name() {
			t.Fatalf("control equals candidate: %q", control.name())
		}
	}
	if controls[0].name() == controls[1].name() {
		t.Fatalf("controls are duplicates: %#v", controls)
	}
}

func TestExactAliasSignatureCapturesManagedPipelineHeaders(t *testing.T) {
	req, _ := http.NewRequest(http.MethodHead, "https://example.test/", nil)
	res := aliasProbeTestResponse(req, http.StatusNotFound, 1234, http.NoBody)
	res.Header.Set("X-AspNet-Version", "4.0.30319")
	res.Header.Set("X-AspNetMvc-Version", "3.0")
	signature := exactAliasSignatureFromResponse(res)
	if signature.AspNetVersion != "4.0.30319" || signature.MVCVersion != "3.0" {
		t.Fatalf("managed pipeline headers missing from signature: %+v", signature)
	}
	for _, want := range []string{`aspnet="4.0.30319"`, `mvc="3.0"`} {
		if !strings.Contains(signature.compact(), want) {
			t.Errorf("compact signature omitted %q: %q", want, signature.compact())
		}
	}
}

func TestBuildLateEncodedExactAliasURLPreservesParserRepresentation(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{SessionStyle: "empty", TildeEncoding: "default"}
	base, err := normalizeExactAliasBase("https://example.test/Content/images", "/")
	if err != nil {
		t.Fatal(err)
	}
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")
	representation, err := newExactAliasRepresentation("late-encoded")
	if err != nil {
		t.Fatal(err)
	}
	rawURL := buildExactAliasProbeURL(base, alias, representation)
	want := "https://example.test/%28S()%29/Content/images/IMAGEM/%28%53%28%29%29%7E1.JPG"
	if rawURL != want {
		t.Fatalf("URL = %q, want %q", rawURL, want)
	}
	req, err := newHTTPRequest(http.MethodHead, rawURL, nil)
	if err != nil {
		t.Fatal(err)
	}
	wantURI := "/%28S()%29/Content/images/IMAGEM/%28%53%28%29%29%7E1.JPG"
	if got := req.URL.RequestURI(); got != wantURI {
		t.Fatalf("RequestURI = %q, want %q", got, wantURI)
	}
	if strings.Contains(req.URL.RequestURI(), "%25") || strings.Contains(req.URL.RequestURI(), "~") {
		t.Fatalf("encoded representation was changed: %q", req.URL.RequestURI())
	}
}

func TestBuildDirectExactAliasURLSupportsSinglePercentTilde(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{TildeEncoding: "percent"}
	base, _ := normalizeExactAliasBase("https://example.test/Content/images/", "/")
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")
	representation, _ := newExactAliasRepresentation("direct")
	rawURL := buildExactAliasProbeURL(base, alias, representation)
	req, err := newHTTPRequest(http.MethodHead, rawURL, nil)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := req.URL.RequestURI(), "/Content/images/IMAGEM%7E1.JPG"; got != want {
		t.Fatalf("RequestURI = %q, want %q", got, want)
	}
}

func TestBuildDirectExactAliasURLSupportsCustomTildeAlias(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{TildeEncoding: "percent"}
	base, _ := normalizeExactAliasBase("https://example.test/h47default/", "/")
	alias, _ := parseExactShortAlias("RCFG~A.TXT")
	representation, _ := newExactAliasRepresentation("direct")
	rawURL := buildExactAliasProbeURL(base, alias, representation)
	req, err := newHTTPRequest(http.MethodHead, rawURL, nil)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := req.URL.RequestURI(), "/h47default/RCFG%7EA.TXT"; got != want {
		t.Fatalf("RequestURI = %q, want %q", got, want)
	}
}

func TestBuildLateAliasURLHonorsNestedApplicationRoot(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{SessionStyle: "empty"}
	base, err := normalizeExactAliasBase("https://example.test/webform/Content/images/", "/webform/")
	if err != nil {
		t.Fatal(err)
	}
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")
	representation, _ := newExactAliasRepresentation("late-encoded")
	got := buildExactAliasProbeURL(base, alias, representation)
	want := "https://example.test/webform/%28S()%29/Content/images/IMAGEM/%28%53%28%29%29%7E1.JPG"
	if got != want {
		t.Fatalf("nested-app URL = %q, want %q", got, want)
	}
	if _, err := normalizeExactAliasBase("https://example.test/other/Content/", "/webform/"); err == nil {
		t.Fatal("base URL outside the declared application root was accepted")
	}
	for _, appRoot := range []string{"webform", "/webform/../", "https://example.test/webform/", "/webform/?x=1"} {
		if _, err := normalizeExactAliasAppRoot(appRoot); err == nil {
			t.Errorf("invalid application root %q was accepted", appRoot)
		}
	}
}

func aliasProbeTestResponse(req *http.Request, status int, length int64, body io.ReadCloser) *http.Response {
	header := make(http.Header)
	header.Set("Content-Type", "text/html; charset=utf-8")
	header.Set("Content-Length", strconv.FormatInt(length, 10))
	return &http.Response{
		StatusCode: status, Status: http.StatusText(status), Header: header,
		ContentLength: length, Body: body, Request: req,
	}
}

func TestProbeExactAliasStableDifferentialUsesHEADAndNeverReadsBody(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{Retries: 0, SessionStyle: "empty", ExactProfile: "late-encoded", ExactMethod: "HEAD", ExactRepeats: 2}
	base, _ := normalizeExactAliasBase("https://example.test/Content/images/", "/")
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")
	reads, closes, requests := 0, 0, 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests++
		if req.Method != http.MethodHead {
			t.Errorf("method = %q, want HEAD", req.Method)
		}
		status, length := http.StatusNotFound, int64(3437)
		if strings.Contains(req.URL.RequestURI(), "/IMAGEM/") {
			status, length = http.StatusBadRequest, 11
		}
		return aliasProbeTestResponse(req, status, length, trackingBody{reads: &reads, closes: &closes}), nil
	})}

	observation, err := probeExactAlias(client, &httpStats{}, base, alias)
	if err != nil {
		t.Fatal(err)
	}
	if !observation.Stable || !observation.Differential || observation.Profile != "late-encoded" {
		t.Fatalf("unexpected observation: %+v", observation)
	}
	if observation.Candidate.Status != http.StatusBadRequest || observation.Control.Status != http.StatusNotFound {
		t.Fatalf("unexpected signatures: %+v", observation)
	}
	if requests != 6 || closes != 6 {
		t.Fatalf("requests=%d closes=%d, want 6/6", requests, closes)
	}
	if reads != 0 {
		t.Fatalf("HEAD response bodies were read %d times", reads)
	}
}

func TestProbeExactAliasRejectsDisagreeingControls(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{Retries: 0, SessionStyle: "empty", ExactProfile: "late-encoded", ExactMethod: "HEAD", ExactRepeats: 2}
	base, _ := normalizeExactAliasBase("https://example.test/Content/images/", "/")
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		status := http.StatusBadRequest
		switch {
		case strings.Contains(req.URL.RequestURI(), "/IMAGEZ/"):
			status = http.StatusNotFound
		case strings.Contains(req.URL.RequestURI(), "/IMAGEQ/"):
			status = http.StatusForbidden
		}
		return aliasProbeTestResponse(req, status, 0, http.NoBody), nil
	})}
	observation, err := probeExactAlias(client, &httpStats{}, base, alias)
	if err != nil {
		t.Fatal(err)
	}
	if observation.Differential || observation.Stable {
		t.Fatalf("disagreeing controls produced a hit: %+v", observation)
	}
	if !strings.Contains(observation.Reason, "controls did not agree") {
		t.Fatalf("unexpected rejection reason: %q", observation.Reason)
	}
}

func TestProbeExactAliasDoesNotPromoteEqualSignatures(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{Retries: 0, SessionStyle: "empty", ExactProfile: "late-encoded", ExactMethod: "HEAD", ExactRepeats: 2}
	base, _ := normalizeExactAliasBase("https://example.test/Content/images/", "/")
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return aliasProbeTestResponse(req, http.StatusNotFound, 3437, http.NoBody), nil
	})}
	observation, err := probeExactAlias(client, &httpStats{}, base, alias)
	if err != nil {
		t.Fatal(err)
	}
	if !observation.Stable || observation.Differential {
		t.Fatalf("equal signatures produced a hit: %+v", observation)
	}
	if !strings.Contains(observation.Reason, "same stable HEAD signature") {
		t.Fatalf("unexpected no-difference reason: %q", observation.Reason)
	}
}

func TestProbeExactAliasRejectsUnstableAndTransientResponses(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	base, _ := normalizeExactAliasBase("https://example.test/Content/images/", "/")
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")

	args = arguments{Retries: 0, SessionStyle: "empty", ExactProfile: "late-encoded", ExactMethod: "HEAD", ExactRepeats: 2}
	candidateRound := 0
	unstableClient := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		status := http.StatusNotFound
		if strings.Contains(req.URL.RequestURI(), "/IMAGEM/") {
			candidateRound++
			status = http.StatusBadRequest
			if candidateRound == 2 {
				status = http.StatusForbidden
			}
		}
		return aliasProbeTestResponse(req, status, 0, http.NoBody), nil
	})}
	observation, err := probeExactAlias(unstableClient, &httpStats{}, base, alias)
	if err != nil || observation.Differential || observation.Stable {
		t.Fatalf("unstable candidate was accepted: observation=%+v err=%v", observation, err)
	}

	args.ExactRepeats = 1
	transientClient := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		status := http.StatusNotFound
		if strings.Contains(req.URL.RequestURI(), "/IMAGEM/") {
			status = http.StatusInternalServerError
		}
		return aliasProbeTestResponse(req, status, 0, http.NoBody), nil
	})}
	observation, err = probeExactAlias(transientClient, &httpStats{}, base, alias)
	if err != nil || observation.Differential || !observation.Stable {
		t.Fatalf("transient response handling: observation=%+v err=%v", observation, err)
	}
	if !strings.Contains(observation.Reason, "server-error") {
		t.Fatalf("unexpected transient rejection reason: %q", observation.Reason)
	}
}

func TestProbeExactAliasAutoStopsAfterFirstWorkingProfile(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{Retries: 0, SessionStyle: "empty", ExactProfile: "auto", ExactMethod: "HEAD", ExactRepeats: 1}
	base, _ := normalizeExactAliasBase("https://example.test/Content/images/", "/")
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")
	requests := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests++
		uri := req.URL.RequestURI()
		if strings.Contains(uri, "~") || strings.Contains(uri, "%25") {
			t.Errorf("auto did not start with the fully encoded profile: %q", uri)
		}
		status := http.StatusNotFound
		if strings.Contains(uri, "/IMAGEM/") {
			status = http.StatusBadRequest
		}
		return aliasProbeTestResponse(req, status, 0, http.NoBody), nil
	})}
	observation, err := probeExactAlias(client, &httpStats{}, base, alias)
	if err != nil || !observation.Differential || observation.Profile != "late-encoded" {
		t.Fatalf("auto observation=%+v err=%v", observation, err)
	}
	if requests != 3 {
		t.Fatalf("auto sent %d requests, want 3", requests)
	}
}

func TestProbeCustomAliasAutoFallsBackFromHEADToOPTIONS(t *testing.T) {
	previousArgs := args
	t.Cleanup(func() { args = previousArgs })
	args = arguments{Retries: 0, ExactProfile: "auto", ExactMethod: "AUTO", ExactRepeats: 1}
	base, _ := normalizeExactAliasBase("https://example.test/h47default/", "/")
	alias, _ := parseExactShortAlias("SRC47.TXT")
	requests := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests++
		status := http.StatusNotFound
		if req.Method == http.MethodOptions && !strings.Contains(req.URL.RequestURI(), "SRC47.TXT") {
			status = http.StatusOK
		}
		if req.Method == http.MethodTrace {
			t.Fatal("TRACE must not run after the OPTIONS differential")
		}
		return aliasProbeTestResponse(req, status, 0, http.NoBody), nil
	})}
	observation, err := probeExactAlias(client, &httpStats{}, base, alias)
	if err != nil {
		t.Fatal(err)
	}
	if !observation.Differential || observation.Profile != "direct" || observation.Method != http.MethodOptions {
		t.Fatalf("unexpected custom-alias observation: %+v", observation)
	}
	if requests != 6 {
		t.Fatalf("requests=%d, want 6 (HEAD and OPTIONS candidate+two controls)", requests)
	}
}

func TestEmitExactAliasObservationMarksLFNAssociationUnverified(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	t.Cleanup(func() { args, outputWriter = previousArgs, previousWriter })
	base, _ := normalizeExactAliasBase("https://example.test/Content/images/", "/")
	alias, _ := parseExactShortAlias("IMAGEM~1.JPG")
	observation := exactAliasObservation{
		Profile: "late-encoded", Method: http.MethodHead, CandidateURL: "https://example.test/probe",
		Candidate: exactAliasSignature{Status: 400, ContentLength: 11},
		Control:   exactAliasSignature{Status: 404, ContentLength: 3437},
		Repeats:   2, Stable: true, Differential: true,
	}

	var human bytes.Buffer
	args = arguments{Output: "human"}
	outputWriter = &human
	emitExactAliasObservation(base, alias, observation, nil)
	if !strings.Contains(human.String(), "LFN association unverified") {
		t.Fatalf("human output overstated the result: %q", human.String())
	}

	var structured bytes.Buffer
	args.Output = "ndjson"
	outputWriter = &structured
	emitExactAliasObservation(base, alias, observation, nil)
	for _, want := range []string{`"type":"alias-differential"`, `"fullmatch":true`, `"shortfile":"IMAGEM"`, `"ordinalverified":false`, `"aliasverified":true`, `"lfnassociationverified":false`, `"method":"HEAD"`} {
		if !strings.Contains(structured.String(), want) {
			t.Errorf("structured output omitted %s: %q", want, structured.String())
		}
	}
}
