package shortscan

import (
	"fmt"
	"net/http"
	"strings"

	"github.com/thezakman/shortscan/pkg/levenshtein"
	"github.com/thezakman/shortscan/pkg/maths"
)

// Tier B multi-oracle fallback (research/53): a body-content differential on
// PROPFIND, tried as the last resort under --auto/--full when every
// status-based oracle has failed — the primary method×suffix matrix AND
// calibrateAltStatusOracle's WebDAV-verb escalation. Unlike those, this is
// DETECTION-ONLY: a real status differential is what drives char-discovery
// and enumerate() everywhere else in the package, and a size-only signal
// can't feed that. A hit still lets --auto correctly report "Vulnerable:
// Yes" on a target where literally no verb yields a status difference,
// instead of silently reporting "No" — ac.method is set to "PROPFIND" like
// any other WebDAV-verb detection, so the existing isWebDAVDetectionVerb()
// warning already tells the operator to fall back to -a allow-copy for
// actual name recovery.
//
// Path-echo trap: IIS's PROPFIND 404 error body echoes the requested path,
// so two DIFFERENT wildcard patterns always produce different bodies even
// when neither corresponds to a real file — a naive len(bodyPos) !=
// len(bodyNeg) check is a false oracle. This calibrates a noise floor from
// several length-matched random wildcards first (the same Levenshtein-ratio
// approach recovery.go's getDistancesForProbe already uses for brute-force
// candidate verification) and only counts a tilde probe as a hit when it
// clears that floor by a real margin, on two independent probes.
//
// Real-world hit rate is unconfirmed: research/53 could not reproduce a
// genuine PROPFIND body-existence signal on the one lab available (IIS
// answered PROPFIND 404 uniformly, dominated by path-echo noise, not
// existence) — Tier B needs a WebDAV-enabled target with real 207-multistatus
// responses to matter at all, hence the webDAVAdvertised precondition below.

// webDAVAdvertised is a cheap single-request precondition check (mirrors
// runFingerprint's own WebDAV detection, kept independent so calibrateSizeOracle
// doesn't depend on --fingerprint having run): PROPFIND-based oracles are only
// worth attempting when the server actually answers WebDAV verbs at all.
func webDAVAdvertised(hc *http.Client, st *httpStats, url string) bool {
	res, err := fetch(hc, st, "OPTIONS", url)
	if err != nil || res == nil {
		return false
	}
	if strings.TrimSpace(res.Header.Get("DAV")) != "" {
		return true
	}
	return strings.Contains(strings.ToUpper(res.Header.Get("Allow")), "PROPFIND")
}

// sizeOracleNoiseFloor samples n length-matched random-wildcard PROPFIND
// probes (a 2-char body, matching a real "~N" pattern's length) and returns
// the samples plus the maximum pairwise Levenshtein ratio among them — the
// noise floor any candidate differential must clear.
func sizeOracleNoiseFloor(hc *http.Client, st *httpStats, url, suffix string, n int) (samples []string, floor float32) {
	for i := 0; i < n; i++ {
		_, body, err := fetchBody(hc, st, "PROPFIND", url+"*"+pathEscape(randAlnum(2))+"*"+suffix, 2048)
		if err != nil {
			continue
		}
		samples = append(samples, string(body))
	}
	for i := 0; i < len(samples); i++ {
		for j := i + 1; j < len(samples); j++ {
			denom := maths.Max(len(samples[i]), len(samples[j]))
			if denom == 0 {
				continue
			}
			if r := float32(levenshtein.Distance(samples[i], samples[j])) / float32(denom); r > floor {
				floor = r
			}
		}
	}
	return samples, floor
}

// calibrateSizeOracle tries a PROPFIND body-content differential for each
// suffix: calibrate a noise floor from random wildcards, then test ~1..~4
// against it, requiring a differential clearly above the floor that
// reproduces on a second independent probe, and rejecting the same ~0
// catch-all pattern the status oracles guard against. DETECTION-ONLY — see
// the file doc comment.
func calibrateSizeOracle(url string, hc *http.Client, st *httpStats, ac *attackConfig, suffixes []string, timedOut func() bool) bool {
	if !webDAVAdvertised(hc, st, url) {
		return false
	}
	// Above getDistancesForProbe's 0.1 margin: this oracle has no status
	// differential to corroborate it, so demand a clearer signal before
	// trusting a pure body-content guess.
	const marginAboveFloor = 0.15
	for _, suffix := range suffixes {
		if timedOut() {
			return false
		}
		samples, floor := sizeOracleNoiseFloor(hc, st, url, suffix, 6)
		if len(samples) < 3 {
			continue // endpoint too unreliable to trust a body-content call here
		}
		baselineBody := samples[0]
		probeDistance := func(pattern string) (float32, bool) {
			_, body, err := fetchBody(hc, st, "PROPFIND", url+pattern+suffix, 2048)
			if err != nil {
				return 0, false
			}
			denom := maths.Max(len(baselineBody), len(body))
			if denom == 0 {
				return 0, false
			}
			return float32(levenshtein.Distance(baselineBody, string(body))) / float32(denom), true
		}
		zeroDist, zeroOK := probeDistance("*" + tildify("~") + "0*")
		var tildes []string
		for i := 1; i <= 4; i++ {
			pattern := "*" + tildify("~") + fmt.Sprintf("%d", i) + "*"
			d1, ok1 := probeDistance(pattern)
			if !ok1 || d1-floor <= marginAboveFloor {
				continue
			}
			// ~0 can't exist; if it shows the same differential the endpoint
			// answers everything alike (catch-all), not a real signal.
			if zeroOK && zeroDist-floor > marginAboveFloor {
				continue
			}
			// Require the differential to reproduce — a one-off body-content
			// blip (timing, dynamic content) is not a stable oracle.
			d2, ok2 := probeDistance(pattern)
			if !ok2 || d2-floor <= marginAboveFloor {
				continue
			}
			tildes = append(tildes, fmt.Sprintf("~%d", i))
		}
		if len(tildes) > 0 {
			ac.tildes = tildes
			ac.method = "PROPFIND"
			ac.suffix = suffix
			ac.detectionOracle = "body-distance"
			// No real status differential exists for this oracle (that's the
			// whole reason it fired) — leaving mk untouched means the
			// downstream status-gated stages (runTildeContinuation,
			// char-discovery) see mk.statusPos == mk.statusNeg and correctly
			// no-op instead of exploding on a false status signal.
			return true
		}
	}
	return false
}
