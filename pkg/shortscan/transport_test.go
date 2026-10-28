package shortscan

import (
	"context"
	"errors"
	"io"
	"net/http"
	"strings"
	"testing"
	"time"
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

func TestRetryBackoffIsBounded(t *testing.T) {
	for _, tc := range []struct {
		attempt    int
		base, want time.Duration
	}{
		{0, time.Second, time.Second}, {3, time.Second, 8 * time.Second},
		{63, time.Second, 30 * time.Second}, {1000000, time.Millisecond, 30 * time.Second},
		{0, time.Hour, 30 * time.Second},
	} {
		if got := retryBackoff(tc.attempt, tc.base); got != tc.want {
			t.Fatalf("backoff=%s want %s", got, tc.want)
		}
	}
}

func TestCanceledRequestDoesNotRetry(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 3, RetryDelay: 60000}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	req, _ := http.NewRequestWithContext(ctx, "GET", "http://example.test/", nil)
	calls := 0
	client := &http.Client{Transport: roundTripFunc(func(*http.Request) (*http.Response, error) {
		calls++
		cancel()
		return nil, context.Canceled
	})}
	var stats httpStats
	_, _, retries, err := sendWithRetry(client, &stats, req)
	if !errors.Is(err, context.Canceled) || calls != 1 || retries != 0 {
		t.Fatalf("calls=%d retries=%d err=%v", calls, retries, err)
	}
}

func TestCancellationInterruptsRetryWait(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{Retries: 3, RetryDelay: 30000}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	req, _ := http.NewRequestWithContext(ctx, "GET", "http://example.test/", nil)
	calls := 0
	client := &http.Client{Transport: roundTripFunc(func(*http.Request) (*http.Response, error) {
		calls++
		time.AfterFunc(20*time.Millisecond, cancel)
		return nil, errors.New("temporary failure")
	})}
	start := time.Now()
	_, _, retries, err := sendWithRetry(client, &httpStats{}, req)
	if !errors.Is(err, context.Canceled) || retries != 0 || calls != 1 {
		t.Fatalf("calls=%d retries=%d err=%v", calls, retries, err)
	}
	if time.Since(start) > time.Second {
		t.Fatal("cancellation did not interrupt retry wait")
	}
}

// countedBody also models a response with far more data than a metadata probe needs.
type countedBody struct {
	remaining int64
	read      int64
	closed    bool
}

func (b *countedBody) Read(p []byte) (int, error) {
	if b.remaining == 0 {
		return 0, io.EOF
	}
	n := min(len(p), int(b.remaining))
	clear(p[:n])
	b.remaining -= int64(n)
	b.read += int64(n)
	return n, nil
}
func (b *countedBody) Close() error { b.closed = true; return nil }

func TestMetadataFetchBoundsBodyAndClosesIt(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{}
	for _, size := range []int64{128, metadataDrainLimit, metadataDrainLimit * 100} {
		body := &countedBody{remaining: size}
		hc := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
			return &http.Response{StatusCode: 200, Header: http.Header{"X-Test": []string{"preserved"}}, Body: body, Request: req}, nil
		})}
		res, err := fetch(hc, &httpStats{}, "GET", "http://example.test/")
		if err != nil {
			t.Fatal(err)
		}
		want := size
		if want > metadataDrainLimit {
			want = metadataDrainLimit
		}
		if body.read != want || !body.closed || res.Body != http.NoBody {
			t.Fatalf("size=%d read=%d closed=%v", size, body.read, body.closed)
		}
		if res.StatusCode != 200 || res.Header.Get("X-Test") != "preserved" {
			t.Fatal("metadata lost")
		}
	}
}
