package shortscan

import (
	"fmt"
	"net/http"
	"testing"
)

func TestRecoveryRejectsTransientInfrastructureResponses(t *testing.T) {
	previousArgs, previousCache := args, statusCache
	previousDistances := distanceCache
	defer func() { args, statusCache, distanceCache = previousArgs, previousCache, previousDistances }()
	args = arguments{}
	for _, mode := range []string{"status", "distance"} {
		for _, candidateStatus := range []int{200, 429, 502, 503, 504} {
			t.Run(fmt.Sprintf("%s/%d", mode, candidateStatus), func(t *testing.T) {
				statusCache = make(map[string]map[int]struct{})
				distanceCache = make(map[string]map[int]distances)
				client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
					code := 404
					if req.URL.Path == "/System.dll" {
						code = candidateStatus
					}
					return responseFor(req, code, "response"), nil
				})}
				candidate := filenameCandidate{record: wordlistRecord{filename: "System", extension: ".dll"}, matchType: "wordlist"}
				res, matched, err := probeAutocompleteCandidate(client, &httpStats{}, &attackConfig{autocomplete: mode}, baseRequest{url: "http://example.test/"}, "http://example.test/", candidate)
				if err != nil || res == nil {
					t.Fatalf("response lost: %v", err)
				}
				if matched != (candidateStatus == 200) {
					t.Fatalf("status=%d matched=%v", candidateStatus, matched)
				}
			})
		}
	}
}

func TestRecoveryRejectsInfrastructureErrorsInBaseline(t *testing.T) {
	previousArgs, previousCache := args, statusCache
	defer func() { args, statusCache = previousArgs, previousCache }()
	args = arguments{}
	for _, code := range []int{429, 502, 503, 504} {
		for _, failDuringEscalation := range []bool{false, true} {
			statusCache = make(map[string]map[int]struct{})
			calls := 0
			client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
				calls++
				baselineStatus := code
				if failDuringEscalation && calls <= 2 {
					baselineStatus = 404
				}
				return responseFor(req, baselineStatus, "missing"), nil
			})}
			if statusExistsAgainstBaseline(wordlistRecord{extension: ".dll"}, baseRequest{url: "http://example.test/"}, client, &httpStats{}, "GET", "", 200) {
				t.Fatalf("accepted contaminated baseline %d escalation=%v", code, failDuringEscalation)
			}
		}
		if matched, _, _ := differsFromDistanceBaseline(200, []byte("file"), map[int]distances{code: {samples: 2, body: "gateway error"}}); matched {
			t.Fatalf("distance accepted contaminated baseline %d", code)
		}
	}
}
