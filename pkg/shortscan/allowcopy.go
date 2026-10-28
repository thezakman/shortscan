package shortscan

import (
	"net/http"
	"sort"
	"strconv"
	"strings"
)

// allowCopySignature models the method-capability differential exposed by the
// IIS native WebDAV module when a PROPFIND reaches StaticFile handling. In the
// affected configuration both an existing and a missing path answer 405; COPY
// is the existence bit in Allow.
type allowCopySignature struct {
	status int
	allow  string
	copy   bool
}

type allowCopyBaseline struct {
	sampled  bool
	valid    bool
	controls [2]string
	sig      allowCopySignature
}

var allowCopyBaselines map[string]allowCopyBaseline

func normaliseAllow(value string, omitCopy bool) (string, bool) {
	seen := make(map[string]struct{})
	hasCopy := false
	for _, item := range strings.Split(value, ",") {
		method := strings.ToUpper(strings.TrimSpace(item))
		if method == "" {
			continue
		}
		if method == "COPY" {
			hasCopy = true
			if omitCopy {
				continue
			}
		}
		seen[method] = struct{}{}
	}
	methods := make([]string, 0, len(seen))
	for method := range seen {
		methods = append(methods, method)
	}
	sort.Strings(methods)
	return strings.Join(methods, ","), hasCopy
}

func allowCopyResponseSignature(res *http.Response) allowCopySignature {
	withoutCopy, hasCopy := normaliseAllow(strings.Join(res.Header.Values("Allow"), ","), true)
	return allowCopySignature{status: res.StatusCode, allow: withoutCopy, copy: hasCopy}
}

func usableAllowCopySignature(sig allowCopySignature, wantCopy bool) bool {
	if sig.status != http.StatusMethodNotAllowed || sig.allow == "" || sig.copy != wantCopy {
		return false
	}
	return true
}

func fetchAllowCopySignature(hc *http.Client, st *httpStats, url string) (*http.Response, allowCopySignature, error) {
	res, err := fetchStatusWithHeaders(hc, st, "PROPFIND", url, map[string]string{
		"Depth":         "0",
		"Cache-Control": "no-cache",
	})
	if err != nil {
		return nil, allowCopySignature{}, err
	}
	return res, allowCopyResponseSignature(res), nil
}

func allowCopyBaselineKey(baseURL, suffix, extension string, stemLength int) string {
	return baseURL + "\x00" + suffix + "\x00" + strings.ToLower(extension) + "\x00" + strconv.Itoa(stemLength)
}

// getAllowCopyBaseline samples two same-extension missing siblings. A baseline
// is usable only when both are stable 405 responses, agree on every advertised
// method, and do not advertise COPY. Invalid baselines are cached as well so a
// catch-all WebDAV configuration cannot multiply controls for every word.
func getAllowCopyBaseline(hc *http.Client, st *httpStats, baseURL, suffix, extension string, stemLength int) allowCopyBaseline {
	key := allowCopyBaselineKey(baseURL, suffix, extension, stemLength)
	cacheMutex.RLock()
	cached, ok := allowCopyBaselines[key]
	cacheMutex.RUnlock()
	if ok && cached.sampled {
		return cached
	}

	baseline := allowCopyBaseline{sampled: true}
	for i := range baseline.controls {
		baseline.controls[i] = baseURL + randPath(stemLength, 0, alphanum) + extension + suffix
		_, sig, err := fetchAllowCopySignature(hc, st, baseline.controls[i])
		if err != nil || !usableAllowCopySignature(sig, false) {
			cacheMutex.Lock()
			if allowCopyBaselines == nil {
				allowCopyBaselines = make(map[string]allowCopyBaseline)
			}
			allowCopyBaselines[key] = baseline
			cacheMutex.Unlock()
			return baseline
		}
		if i == 0 {
			baseline.sig = sig
		} else if sig != baseline.sig {
			cacheMutex.Lock()
			if allowCopyBaselines == nil {
				allowCopyBaselines = make(map[string]allowCopyBaseline)
			}
			allowCopyBaselines[key] = baseline
			cacheMutex.Unlock()
			return baseline
		}
	}
	baseline.valid = true
	cacheMutex.Lock()
	if allowCopyBaselines == nil {
		allowCopyBaselines = make(map[string]allowCopyBaseline)
	}
	allowCopyBaselines[key] = baseline
	cacheMutex.Unlock()
	return baseline
}

// allowCopyExistsAgainstBaseline confirms an apparent COPY capability with a
// second candidate request and a second pass over both controls. Requiring the
// candidate's remaining Allow set to equal the controls makes COPY the sole
// promoted difference and rejects generic/catch-all DAV advertising.
func allowCopyExistsAgainstBaseline(hc *http.Client, st *httpStats, baseURL, candidatePath, suffix, extension string) (*http.Response, bool, error) {
	candidateURL := baseURL + candidatePath + suffix
	res, candidate, err := fetchAllowCopySignature(hc, st, candidateURL)
	if err != nil || !usableAllowCopySignature(candidate, true) {
		return res, false, err
	}
	escapedExtension := pathEscape(extension)
	stemLength := len(candidatePath) - len(escapedExtension)
	if stemLength < 1 || !strings.EqualFold(candidatePath[len(candidatePath)-len(escapedExtension):], escapedExtension) {
		stemLength = len(candidatePath)
	}
	baseline := getAllowCopyBaseline(hc, st, baseURL, suffix, extension, stemLength)
	if !baseline.valid || candidate.status != baseline.sig.status || candidate.allow != baseline.sig.allow {
		return res, false, nil
	}

	_, repeatedCandidate, err := fetchAllowCopySignature(hc, st, candidateURL)
	if err != nil || repeatedCandidate != candidate {
		return res, false, err
	}
	for _, controlURL := range baseline.controls {
		_, repeatedControl, controlErr := fetchAllowCopySignature(hc, st, controlURL)
		if controlErr != nil || repeatedControl != baseline.sig {
			return res, false, controlErr
		}
	}
	return res, true, nil
}
