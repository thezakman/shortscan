package shortscan

import "net/http"

// oracleProfile is one stable view of the IIS short-name predicate. Profiles
// are intentionally keyed by method and suffix as well as their response
// markers: two handlers can expose disjoint aliases even when both use the
// same 200/404 pair.
type oracleProfile struct {
	method          string
	suffix          string
	detectionOracle string
	markersByTilde  map[string]markers
	tildes          []string
	fileChars       map[string]string
	extChars        map[string]string
	dotExtChars     map[string]string
}

func (p *oracleProfile) fetch(hc *http.Client, st *httpStats, rawURL string) (*http.Response, error) {
	if p == nil {
		return nil, nil
	}
	return fetch(hc, st, p.method, rawURL+p.suffix)
}

func (p *oracleProfile) matchesPositive(tilde string, res *http.Response) bool {
	mk, ok := p.markerForTilde(tilde)
	return ok && responseMatchesPositive(res, mk) && !isTransientInfraStatus(res.StatusCode)
}

// matchesNonNegative preserves the legacy exact-alias / %3f* semantics, but
// evaluates the response only against the marker belonging to this profile.
// A third stable class can therefore confirm an exact alias without letting a
// different method/suffix lend its negative baseline to the decision.
func (p *oracleProfile) matchesNonNegative(tilde string, res *http.Response) bool {
	mk, ok := p.markerForTilde(tilde)
	return ok && res != nil && !responseMatchesNegative(res, mk) && !isTransientInfraStatus(res.StatusCode)
}

func copyMarkersByTilde(in map[string]markers) map[string]markers {
	out := make(map[string]markers, len(in))
	for tilde, mk := range in {
		out[tilde] = mk
	}
	return out
}

func appendUniqueTilde(dst []string, tilde string) []string {
	for _, existing := range dst {
		if existing == tilde {
			return dst
		}
	}
	return append(dst, tilde)
}

func (p *oracleProfile) markerForTilde(tilde string) (markers, bool) {
	if p == nil {
		return markers{}, false
	}
	mk, ok := p.markersByTilde[tilde]
	return mk, ok
}

// installBatchOracleProfiles retains every stable combo that was already
// executed in the winning concurrent batch. This adds coverage without one
// extra request compared with the old first-winner behavior.
func installBatchOracleProfiles(ac *attackConfig, mk *markers, results []matrixProbeResult) bool {
	installed := false
	primaryInstalled := len(ac.oracleProfiles) > 0
	for _, result := range results {
		if len(result.tildes) == 0 {
			continue
		}
		profile := oracleProfile{
			method:          result.method,
			suffix:          result.suffix,
			detectionOracle: "status",
			markersByTilde:  copyMarkersByTilde(result.markersByTilde),
			tildes:          append([]string(nil), result.tildes...),
		}
		ac.oracleProfiles = append(ac.oracleProfiles, profile)
		for _, tilde := range result.tildes {
			ac.tildes = appendUniqueTilde(ac.tildes, tilde)
		}
		installed = true
		if !primaryInstalled {
			primaryInstalled = true
			ac.method, ac.suffix = result.method, result.suffix
			ac.markersByTilde = copyMarkersByTilde(result.markersByTilde)
			if primary, ok := profile.markerForTilde(profile.tildes[0]); ok {
				*mk = primary
			}
		}
	}
	return installed
}

// ensureLegacyOracleProfile adapts the existing header/alt-status fallbacks to
// the portfolio interface. The body-distance fallback is detection-only and
// deliberately has no usable markers, so it is not installed here.
func ensureLegacyOracleProfile(ac *attackConfig, mk markers) {
	if len(ac.oracleProfiles) > 0 || len(ac.tildes) == 0 || !markerUsable(mk) || ac.detectionOracle == "body-distance" {
		return
	}
	oracle := ac.detectionOracle
	if oracle == "" {
		oracle = "status"
	}
	byTilde := make(map[string]markers, len(ac.tildes))
	for _, tilde := range ac.tildes {
		byTilde[tilde] = mk
	}
	ac.oracleProfiles = append(ac.oracleProfiles, oracleProfile{
		method: ac.method, suffix: ac.suffix, detectionOracle: oracle,
		markersByTilde: byTilde, tildes: append([]string(nil), ac.tildes...),
	})
}

func (ac *attackConfig) profilesForTilde(tilde string) []*oracleProfile {
	profiles := make([]*oracleProfile, 0, len(ac.oracleProfiles))
	for i := range ac.oracleProfiles {
		if _, ok := ac.oracleProfiles[i].markerForTilde(tilde); ok {
			profiles = append(profiles, &ac.oracleProfiles[i])
		}
	}
	return profiles
}

// probeOracleURL sends one candidate through every calibrated profile that
// supports its ordinal. It returns the first typed positive in deterministic
// matrix order. A status belonging to a different ordinal/profile is never
// accepted merely because it differs from the negative baseline.
func probeOracleURL(hc *http.Client, st *httpStats, ac *attackConfig, tilde, rawURL string) (*http.Response, *oracleProfile, bool, error) {
	var lastRes *http.Response
	var lastProfile *oracleProfile
	var lastErr error
	for _, profile := range ac.profilesForTilde(tilde) {
		res, err := fetch(hc, st, profile.method, rawURL+profile.suffix)
		if err != nil {
			lastErr = err
			continue
		}
		lastRes, lastProfile = res, profile
		mk, _ := profile.markerForTilde(tilde)
		if responseMatchesPositive(res, mk) && !isTransientInfraStatus(res.StatusCode) {
			return res, profile, true, nil
		}
	}
	if lastRes != nil {
		return lastRes, lastProfile, false, nil
	}
	return nil, nil, false, lastErr
}

func detectionEvidence(profile *oracleProfile, res *http.Response) (oracle, method, suffix string, status int) {
	if profile == nil {
		return "", "", "", 0
	}
	if res != nil {
		status = res.StatusCode
	}
	return profile.detectionOracle, profile.method, profile.suffix, status
}
