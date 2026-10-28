package shortscan

import (
	"net/http"
	"strconv"
	"strings"
)

// Translate: f is the Microsoft WebDAV request for a resource's unprocessed
// representation.  IIS can reject a real resource at the source-access check
// (observed 401) while an unmapped sibling reaches ordinary 404, making it a
// useful exact-LFN oracle even when no bytes are disclosed.
//
// This is still a GET. A server that ignores Translate may execute/process the
// resource normally, so the oracle is opt-in and never presented as universally
// non-executing.
type translateBaseline struct {
	sampled  bool
	valid    bool
	controls [2]string
	status   int
}

var translateBaselines map[string]translateBaseline

func translateBaselineKey(baseURL, suffix, extension string, stemLength int) string {
	return baseURL + "\x00" + suffix + "\x00" + strings.ToLower(extension) + "\x00" + strconv.Itoa(stemLength)
}

func fetchTranslateStatus(hc *http.Client, st *httpStats, url string) (*http.Response, error) {
	return fetchStatusWithHeaders(hc, st, http.MethodGet, url, map[string]string{
		"Translate":     "f",
		"Cache-Control": "no-cache",
	})
}

func getTranslateBaseline(hc *http.Client, st *httpStats, baseURL, suffix, extension string, stemLength int) translateBaseline {
	key := translateBaselineKey(baseURL, suffix, extension, stemLength)
	cacheMutex.RLock()
	cached, ok := translateBaselines[key]
	cacheMutex.RUnlock()
	if ok && cached.sampled {
		return cached
	}

	baseline := translateBaseline{sampled: true}
	for i := range baseline.controls {
		baseline.controls[i] = baseURL + randPath(stemLength, 0, alphanum) + extension + suffix
		res, err := fetchTranslateStatus(hc, st, baseline.controls[i])
		if err != nil || res == nil {
			cacheMutex.Lock()
			if translateBaselines == nil {
				translateBaselines = make(map[string]translateBaseline)
			}
			translateBaselines[key] = baseline
			cacheMutex.Unlock()
			return baseline
		}
		if i == 0 {
			baseline.status = res.StatusCode
		} else if res.StatusCode != baseline.status {
			cacheMutex.Lock()
			if translateBaselines == nil {
				translateBaselines = make(map[string]translateBaseline)
			}
			translateBaselines[key] = baseline
			cacheMutex.Unlock()
			return baseline
		}
	}
	baseline.valid = true
	cacheMutex.Lock()
	if translateBaselines == nil {
		translateBaselines = make(map[string]translateBaseline)
	}
	translateBaselines[key] = baseline
	cacheMutex.Unlock()
	return baseline
}

// translateExistsAgainstBaseline accepts a candidate only when its status is
// different from two stable same-extension misses, then repeats the candidate
// and both controls.  This is the same false-positive discipline as Allow/COPY.
func translateExistsAgainstBaseline(hc *http.Client, st *httpStats, baseURL, candidatePath, suffix, extension string) (*http.Response, bool, error) {
	candidateURL := baseURL + candidatePath + suffix
	res, err := fetchTranslateStatus(hc, st, candidateURL)
	if err != nil || res == nil {
		return res, false, err
	}
	escapedExtension := pathEscape(extension)
	stemLength := len(candidatePath) - len(escapedExtension)
	if stemLength < 1 || !strings.EqualFold(candidatePath[len(candidatePath)-len(escapedExtension):], escapedExtension) {
		stemLength = len(candidatePath)
	}
	baseline := getTranslateBaseline(hc, st, baseURL, suffix, extension, stemLength)
	if !baseline.valid || res.StatusCode == baseline.status {
		return res, false, nil
	}

	repeat, err := fetchTranslateStatus(hc, st, candidateURL)
	if err != nil || repeat == nil || repeat.StatusCode != res.StatusCode {
		return res, false, err
	}
	for _, controlURL := range baseline.controls {
		control, controlErr := fetchTranslateStatus(hc, st, controlURL)
		if controlErr != nil || control == nil || control.StatusCode != baseline.status {
			return res, false, controlErr
		}
	}
	return res, true, nil
}
