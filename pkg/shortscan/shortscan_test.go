package shortscan

import (
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
	"time"
)

func TestDetectFingerprintIIS10(t *testing.T) {
	h := http.Header{}
	h.Set("Server", "Microsoft-IIS/10.0")
	h.Set("X-Aspnet-Version", "4.0.30319")
	fp := detectFingerprint(h)
	if !fp.isIIS {
		t.Errorf("expected isIIS=true; got %+v", fp)
	}
	if fp.majorVersion != 10 {
		t.Errorf("expected majorVersion=10; got %d", fp.majorVersion)
	}
	if !fp.aspNet {
		t.Errorf("expected aspNet=true; got %+v", fp)
	}
}

func TestDetectFingerprintKestrel(t *testing.T) {
	h := http.Header{}
	h.Set("Server", "Kestrel")
	h.Set("X-Powered-By", "ASP.NET")
	fp := detectFingerprint(h)
	if !fp.kestrelFront {
		t.Errorf("expected kestrelFront=true; got %+v", fp)
	}
	if !fp.aspNet {
		t.Errorf("expected aspNet=true; got %+v", fp)
	}
}

func TestDetectFingerprintWAFMarker(t *testing.T) {
	h := http.Header{}
	h.Set("Server", "cloudflare")
	h.Set("Cf-Ray", "abc123-IAD")
	fp := detectFingerprint(h)
	if !fp.hasWAFMarkers {
		t.Errorf("expected hasWAFMarkers=true; got %+v", fp)
	}
}

func TestPrioritiseProbeOrderIIS10(t *testing.T) {
	fp := iisFingerprint{majorVersion: 10, isIIS: true}
	suffixes := []string{"/", "", "/.aspx", "/.asmx", "/.svc", "/.ashx"}
	methods := []string{"OPTIONS", "HEAD", "TRACE", "DEBUG", "GET"}
	s, m := prioritiseProbeOrder(fp, suffixes, methods)
	if m[0] != "OPTIONS" {
		t.Errorf("expected OPTIONS first for IIS 10; got %q (full: %v)", m[0], m)
	}
	if s[0] != "/.aspx" {
		t.Errorf("expected /.aspx first for IIS 10; got %q (full: %v)", s[0], s)
	}
	if len(m) != len(methods) || len(s) != len(suffixes) {
		t.Errorf("reordering changed slice length: m=%d want=%d, s=%d want=%d", len(m), len(methods), len(s), len(suffixes))
	}
}

func TestPrioritiseProbeOrderIIS6(t *testing.T) {
	fp := iisFingerprint{majorVersion: 6, isIIS: true}
	suffixes := []string{"/", "", "/.aspx"}
	methods := []string{"OPTIONS", "GET", "HEAD"}
	s, m := prioritiseProbeOrder(fp, suffixes, methods)
	if m[0] != "OPTIONS" {
		t.Errorf("expected OPTIONS first for IIS 6; got %q", m[0])
	}
	if s[0] != "/" {
		t.Errorf("expected / first for IIS 6; got %q", s[0])
	}
}

func TestRateLimiterInterval(t *testing.T) {
	rl := newRateLimiter(100, false) // 100 rps -> 10ms interval
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	start := time.Now()
	for i := 0; i < 5; i++ {
		if err := rl.Wait(ctx); err != nil {
			t.Fatalf("Wait returned error: %v", err)
		}
	}
	elapsed := time.Since(start)
	// 5 tokens at 100 rps should take >= 40ms (first is free, 4 intervals).
	if elapsed < 30*time.Millisecond {
		t.Errorf("rate limiter did not pace: elapsed=%v", elapsed)
	}
}

func TestRateLimiterDisabledByDefault(t *testing.T) {
	rl := newRateLimiter(0, false)
	if rl.enabled {
		t.Errorf("expected rate limiter disabled when rps=0 and adaptive=false")
	}
	// Wait should be a no-op.
	if err := rl.Wait(context.Background()); err != nil {
		t.Errorf("Wait on disabled limiter should not error: %v", err)
	}
}

func TestRateLimiterThrottle(t *testing.T) {
	rl := newRateLimiter(1000, true) // 1ms interval, adaptive on
	rl.Throttle(50 * time.Millisecond)
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	start := time.Now()
	if err := rl.Wait(ctx); err != nil {
		t.Fatalf("Wait returned error: %v", err)
	}
	elapsed := time.Since(start)
	if elapsed < 40*time.Millisecond {
		t.Errorf("throttle penalty not applied: elapsed=%v", elapsed)
	}
}

func TestCheckpointReplay(t *testing.T) {
	dir := t.TempDir()
	cp := filepath.Join(dir, "state.ndjson")

	// Seed the file with a hit + a visit record.
	fh, err := os.Create(cp)
	if err != nil {
		t.Fatal(err)
	}
	recs := []checkpointRecord{
		{Type: "visit", URL: "https://example.com/"},
		{Type: "hit", URL: "https://example.com/", FullPath: "robots.txt"},
	}
	for _, r := range recs {
		b, _ := json.Marshal(r)
		fh.Write(b)
		fh.Write([]byte("\n"))
	}
	fh.Close()

	w, state, visits, err := newCheckpointWriter(cp)
	if err != nil {
		t.Fatalf("unable to open checkpoint: %v", err)
	}
	defer w.close()

	if _, ok := visits["https://example.com/"]; !ok {
		t.Errorf("expected visit replay; got %v", visits)
	}
	if _, ok := state["https://example.com/"]["robots.txt"]; !ok {
		t.Errorf("expected hit replay; got %v", state)
	}

	// Appending should work and survive a reopen.
	w.write(checkpointRecord{Type: "hit", URL: "https://example.com/", FullPath: "web.config.bak"})

	_, state2, _, err := newCheckpointWriter(cp)
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := state2["https://example.com/"]["web.config.bak"]; !ok {
		t.Errorf("expected append to be persisted; got %v", state2)
	}
}

func TestHashBucketPopulation(t *testing.T) {
	// Populate a bucket manually and assert hashHit logic on a canned response.
	hashCache = map[string]map[int]*hashBucket{
		".txt": {
			404: {sums: map[string]struct{}{}, minLen: 100, maxLen: 200, populated: true},
		},
	}
	// Known miss SHA (body "abc") should not hit; new SHA should.
	// We simulate by only checking the bucket membership.
	h := hashCache[".txt"][404]
	if _, ok := h.sums["deadbeef"]; ok {
		t.Errorf("unexpected key in empty bucket")
	}
	h.sums["known"] = struct{}{}
	if _, ok := h.sums["known"]; !ok {
		t.Errorf("bucket insert failed")
	}
}

func TestPathSuffixesContainExtras(t *testing.T) {
	want := []string{"/.ashx", "/.svc", "\\", "::$DATA", ".", "/a.aspx"}
	got := strings.Join(pathSuffixes[:], "|")
	for _, w := range want {
		if !strings.Contains(got, "|"+w+"|") && !strings.HasPrefix(got, w+"|") && !strings.HasSuffix(got, "|"+w) {
			t.Errorf("expected pathSuffixes to contain %q; got %v", w, pathSuffixes)
		}
	}
}

func TestFetchWithOverrideSmugglesVerb(t *testing.T) {
	var seenMethod atomic.Value
	var seenOverride atomic.Value
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		seenMethod.Store(r.Method)
		seenOverride.Store(r.Header.Get("X-HTTP-Method-Override"))
		w.WriteHeader(http.StatusOK)
	}))
	defer srv.Close()

	// Arrange globals the function reads from: User-Agent override is fine empty.
	args = arguments{}
	globalLimiter = nil

	hc := &http.Client{Timeout: 5 * time.Second}
	st := &httpStats{}

	// Direct verb.
	_, err := fetchWithOverride(hc, st, "DEBUG", "", srv.URL+"/")
	if err != nil {
		t.Fatalf("direct fetch failed: %v", err)
	}
	if got := seenMethod.Load().(string); got != "DEBUG" {
		t.Errorf("expected wire method DEBUG; got %q", got)
	}
	if got := seenOverride.Load().(string); got != "" {
		t.Errorf("expected no override header on direct fetch; got %q", got)
	}

	// Via override.
	_, err = fetchWithOverride(hc, st, "DEBUG", "POST", srv.URL+"/")
	if err != nil {
		t.Fatalf("override fetch failed: %v", err)
	}
	if got := seenMethod.Load().(string); got != "POST" {
		t.Errorf("expected wire method POST when overriding; got %q", got)
	}
	if got := seenOverride.Load().(string); got != "DEBUG" {
		t.Errorf("expected X-HTTP-Method-Override=DEBUG; got %q", got)
	}
}

func TestFetchAdaptiveThrottleOn429(t *testing.T) {
	var hits int32
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		n := atomic.AddInt32(&hits, 1)
		if n == 1 {
			w.Header().Set("Retry-After", "1")
			w.WriteHeader(http.StatusTooManyRequests)
			return
		}
		w.WriteHeader(http.StatusOK)
	}))
	defer srv.Close()

	args = arguments{}
	globalLimiter = newRateLimiter(0, true) // adaptive only, no hard rps
	hc := &http.Client{Timeout: 5 * time.Second}
	st := &httpStats{}

	// First call returns 429 -> throttle penalty.
	if _, err := fetchWithOverride(hc, st, "GET", "", srv.URL+"/"); err != nil {
		t.Fatalf("first fetch failed: %v", err)
	}

	start := time.Now()
	if _, err := fetchWithOverride(hc, st, "GET", "", srv.URL+"/"); err != nil {
		t.Fatalf("second fetch failed: %v", err)
	}
	elapsed := time.Since(start)
	if elapsed < 500*time.Millisecond {
		t.Errorf("expected Retry-After to pace second request >= 500ms; got %v", elapsed)
	}
}

func TestReservedNamesList(t *testing.T) {
	if len(reservedNames) < 20 {
		t.Errorf("reserved names list looks truncated: %d entries", len(reservedNames))
	}
	has := map[string]bool{}
	for _, n := range reservedNames {
		has[n] = true
	}
	for _, must := range []string{"CON", "PRN", "AUX", "NUL", "COM1", "LPT9"} {
		if !has[must] {
			t.Errorf("reservedNames missing %q", must)
		}
	}
}
