package shortscan

import (
	"net/http"
	"strings"
	"testing"
)

func flattenedHeaderOracleTransport(catchAll bool) roundTripFunc {
	return func(req *http.Request) (*http.Response, error) {
		res := responseFor(req, http.StatusNotFound, "flattened")
		path := req.URL.EscapedPath()
		positive := strings.Contains(path, "~1") && !strings.Contains(path, "~0")
		if catchAll && strings.Contains(path, "~0") {
			positive = true
		}
		if positive {
			res.Header.Set("Content-Type", "text/html; charset=utf-8")
		}
		return res, nil
	}
}

func TestHeaderOracleCalibratesAndMatches(t *testing.T) {
	hc := &http.Client{Transport: flattenedHeaderOracleTransport(false)}
	ac := &attackConfig{}
	mk := &markers{}
	if !calibrateHeaderOracle("http://edge.test/", hc, &httpStats{}, ac, mk,
		[]string{"OPTIONS"}, []string{"/"}, func() bool { return false }) {
		t.Fatal("stable header differential was not calibrated")
	}
	if !mk.headerOracle || mk.statusPos != http.StatusNotFound || mk.statusNeg != http.StatusNotFound {
		t.Fatalf("unexpected markers: %+v", *mk)
	}
	if ac.method != "OPTIONS" || ac.detectionOracle != "header-signature" {
		t.Fatalf("unexpected attack config: method=%q oracle=%q", ac.method, ac.detectionOracle)
	}
	pos, _ := hc.Get("http://edge.test/*~1*/")
	neg, _ := hc.Get("http://edge.test/*AA*/")
	if !responseMatchesPositive(pos, *mk) || responseMatchesPositive(neg, *mk) {
		t.Fatal("positive header class did not discriminate candidate from control")
	}
	if !responseMatchesNegative(neg, *mk) || responseMatchesNegative(pos, *mk) {
		t.Fatal("negative header class did not discriminate control from candidate")
	}
}

func TestHeaderOracleRejectsTildeZeroCatchAll(t *testing.T) {
	hc := &http.Client{Transport: flattenedHeaderOracleTransport(true)}
	if calibrateHeaderOracle("http://edge.test/", hc, &httpStats{}, &attackConfig{}, &markers{},
		[]string{"OPTIONS"}, []string{"/"}, func() bool { return false }) {
		t.Fatal("~0 catch-all was accepted as a header oracle")
	}
}

func TestHeaderOracleIgnoresContentLengthOnlyNoise(t *testing.T) {
	hc := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		res := responseFor(req, http.StatusNotFound, "same")
		res.ContentLength = int64(len(req.URL.EscapedPath()))
		return res, nil
	})}
	if calibrateHeaderOracle("http://edge.test/", hc, &httpStats{}, &attackConfig{}, &markers{},
		[]string{"OPTIONS"}, []string{"/"}, func() bool { return false }) {
		t.Fatal("path-length-only Content-Length variation was accepted")
	}
}

func TestHeaderOracleNoteSurvivesDisabledRecovery(t *testing.T) {
	got := oracleNote("none", "OPTIONS", "header-signature")
	if !strings.Contains(got, "header signature via OPTIONS") {
		t.Fatalf("header detection oracle disappeared when recovery was disabled: %q", got)
	}
}
