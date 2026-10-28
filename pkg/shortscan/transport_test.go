package shortscan

import (
	"errors"
	"io"
	"net/http"
	"strings"
	"testing"
)

// TestTotalFailureRecordsStats guards against a bug where every fetch*/executeRequest
// caller returns immediately on a total transport failure (all retries exhausted)
// before ever reaching its own recordHTTPStats call, leaving the retried-then-failed
// attempts against an unreachable host invisible in the final "Requests/Retries"
// summary. sendWithRetry must record the attempt itself on that path.
func TestTotalFailureRecordsStats(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 3, RetryDelay: 1}

	calls := 0
	hc := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		calls++
		return nil, errors.New("connection refused")
	})}

	var st httpStats
	_, err := fetch(hc, &st, "GET", "http://127.0.0.1:1/nope")
	if err == nil {
		t.Fatal("expected a transport error")
	}
	if calls != 4 { // 1 initial + 3 retries
		t.Fatalf("expected 4 attempts, got %d", calls)
	}
	st.Lock()
	requests, retries := st.requests, st.retries
	st.Unlock()
	if requests != 1 {
		t.Errorf("st.requests = %d, want 1 (one logical request, regardless of retry count)", requests)
	}
	if retries != 3 {
		t.Errorf("st.retries = %d, want 3", retries)
	}
}

func TestRetryStopsWhenRequestBodyCannotRewind(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 2, RetryDelay: 1}

	request, err := http.NewRequest("PROPFIND", "http://example.test/", strings.NewReader("body"))
	if err != nil {
		t.Fatal(err)
	}
	request.GetBody = func() (io.ReadCloser, error) { return nil, errors.New("rewind failed") }
	calls := 0
	client := &http.Client{Transport: roundTripFunc(func(*http.Request) (*http.Response, error) {
		calls++
		return nil, errors.New("temporary transport failure")
	})}
	var stats httpStats
	_, _, retries, err := sendWithRetry(client, &stats, request)
	if err == nil || !strings.Contains(err.Error(), "rewind failed") {
		t.Fatalf("expected rewind error, got %v", err)
	}
	if calls != 1 || retries != 0 || stats.requests != 1 || stats.retries != 0 {
		t.Fatalf("calls=%d retries=%d requests=%d stats.retries=%d", calls, retries, stats.requests, stats.retries)
	}
}
