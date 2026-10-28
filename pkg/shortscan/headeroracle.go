package shortscan

import (
	"fmt"
	"net/http"
	"strings"
)

// responseHeaderClass deliberately excludes Content-Length and Location: IIS
// error pages often echo the request path, so both fields can vary with probe
// length without saying anything about filesystem existence. These fields are
// categorical response metadata that a status-normalising edge commonly leaves
// intact when it forwards the origin response body.
type responseHeaderClass struct {
	ContentType   string
	Allow         string
	DAV           string
	Authenticate  string
	ContentCoding string
	AspNetVersion string
	MVCVersion    string
}

func headerClass(res *http.Response) responseHeaderClass {
	if res == nil {
		return responseHeaderClass{}
	}
	return responseHeaderClass{
		ContentType:   strings.ToLower(strings.TrimSpace(res.Header.Get("Content-Type"))),
		Allow:         normalizeHeaderSet(res.Header.Get("Allow")),
		DAV:           normalizeHeaderSet(res.Header.Get("DAV")),
		Authenticate:  strings.ToLower(strings.TrimSpace(res.Header.Get("WWW-Authenticate"))),
		ContentCoding: strings.ToLower(strings.TrimSpace(res.Header.Get("Content-Encoding"))),
		AspNetVersion: strings.TrimSpace(res.Header.Get("X-AspNet-Version")),
		MVCVersion:    strings.TrimSpace(res.Header.Get("X-AspNetMvc-Version")),
	}
}

func responseMatchesPositive(res *http.Response, mk markers) bool {
	if res == nil {
		return false
	}
	if mk.headerOracle {
		return res.StatusCode == mk.statusPos && headerClass(res) == mk.headerPos
	}
	return res.StatusCode == mk.statusPos
}

func responseMatchesNegative(res *http.Response, mk markers) bool {
	if res == nil {
		return false
	}
	if mk.headerOracle {
		return res.StatusCode == mk.statusNeg && headerClass(res) == mk.headerNeg
	}
	return res.StatusCode == mk.statusNeg
}

func markerUsable(mk markers) bool {
	if mk.headerOracle {
		return mk.statusPos != 0 && mk.headerPos != mk.headerNeg
	}
	return mk.statusPos != 0 && mk.statusPos != mk.statusNeg
}

// calibrateHeaderOracle is the last fully-enumerable fallback after every
// status oracle fails. It targets reverse proxies/WAFs that rewrite all origin
// statuses to one value while preserving categorical response headers. Four
// same-shape random baselines must agree; ~0 must remain negative; a positive
// tilde must reproduce. Content length is intentionally not part of the signal.
func calibrateHeaderOracle(url string, hc *http.Client, st *httpStats, ac *attackConfig, mk *markers, methods, suffixes []string, timedOut func() bool) bool {
	for _, suffix := range suffixes {
		for _, method := range methods {
			if timedOut() {
				return false
			}
			var negStatus int
			var negClass responseHeaderClass
			stable := true
			for i := 0; i < 4; i++ {
				res, err := fetch(hc, st, method, url+"*"+pathEscape(randAlnum(2))+"*"+suffix)
				if err != nil || res == nil || isTransientInfraStatus(res.StatusCode) {
					stable = false
					break
				}
				c := headerClass(res)
				if i > 0 && (res.StatusCode != negStatus || c != negClass) {
					stable = false
					break
				}
				negStatus, negClass = res.StatusCode, c
			}
			if !stable || negStatus == 0 {
				continue
			}

			zero, err := fetch(hc, st, method, url+"*"+tildify("~")+"0*"+suffix)
			if err != nil || zero == nil || zero.StatusCode != negStatus || headerClass(zero) != negClass {
				continue
			}

			var posClass responseHeaderClass
			var tildes []string
			for i := 1; i <= 4; i++ {
				pattern := "*" + tildify("~") + fmt.Sprintf("%d", i) + "*"
				first, err := fetch(hc, st, method, url+pattern+suffix)
				if err != nil || first == nil || first.StatusCode != negStatus {
					continue
				}
				candidateClass := headerClass(first)
				if candidateClass == negClass {
					continue
				}
				repeat, err := fetch(hc, st, method, url+pattern+suffix)
				if err != nil || repeat == nil || repeat.StatusCode != negStatus || headerClass(repeat) != candidateClass {
					continue
				}
				if len(tildes) == 0 {
					posClass = candidateClass
				}
				if candidateClass == posClass {
					tildes = append(tildes, fmt.Sprintf("~%d", i))
				}
			}
			if len(tildes) == 0 {
				continue
			}

			ac.tildes = tildes
			ac.method = method
			ac.suffix = suffix
			ac.detectionOracle = "header-signature"
			mk.statusPos = negStatus
			mk.statusNeg = negStatus
			mk.headerOracle = true
			mk.headerPos = posClass
			mk.headerNeg = negClass
			return true
		}
	}
	return false
}
