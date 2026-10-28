package shortscan

import (
	"net/http"
	"sync"
	"testing"
)

// TestStatusBaselineNoRaceUnderConcurrency reproduces the v0.51.x data race: the
// --probe-candidates brute path calls statusExistsAgainstBaseline from concurrent
// enumerate() workers without holding autocompleteMutex, and escalateStatusBaseline
// used to mutate the shared cached map in place while other workers read it — a
// fatal "concurrent map read and map write" throw. Run with `-race`; it must pass.
func TestStatusBaselineNoRaceUnderConcurrency(t *testing.T) {
	prevArgs, prevCache := args, statusCache
	defer func() { args, statusCache = prevArgs, prevCache }()
	args = arguments{Retries: 0, RetryDelay: 1}
	statusCache = make(map[string]map[int]struct{})

	// Baseline probes all miss (404); the candidate status 200 is "unseen", which
	// drives escalateStatusBaseline — the map-mutation path — on every call.
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}
	c := wordlistRecord{extension: ".aspx"}
	br := baseRequest{url: "http://race.test/"}

	var wg sync.WaitGroup
	for i := 0; i < 16; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < 25; j++ {
				statusExistsAgainstBaseline(c, br, client, &httpStats{}, "GET", "/", http.StatusOK)
			}
		}()
	}
	wg.Wait()
}
