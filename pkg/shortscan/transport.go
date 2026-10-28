package shortscan

import (
	"crypto/tls"
	"fmt"
	"io"
	"math/rand"
	"net/http"
	"net/http/httputil"
	nurl "net/url"
	"strings"
	"sync"
	"time"

	log "github.com/sirupsen/logrus"
)

type httpStats struct {
	sync.Mutex
	bytesTx  int
	bytesRx  int
	requests int
	retries  int
}

// addRequests folds externally-counted requests (e.g. the raw-socket / ALPN-h2
// desync probes, which bypass the counted HTTP client) into the stats.
func (s *httpStats) addRequests(n int) {
	if s == nil || n == 0 {
		return
	}
	s.Lock()
	s.requests += n
	s.Unlock()
}

// Rate limiter state (req/s); zero disables limiting
var (
	requestDelay    time.Duration
	lastRequestTime time.Time
	rateMutex       sync.Mutex
)

// delayRequest blocks the caller until enough time has passed since the last request
func delayRequest() {
	if requestDelay == 0 {
		return
	}
	rateMutex.Lock()
	defer rateMutex.Unlock()
	if d := time.Until(lastRequestTime.Add(requestDelay)); d > 0 {
		time.Sleep(d)
	}
	lastRequestTime = time.Now()
}

// User-Agent pool used when --random-agent is set
var userAgentPool = []string{
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Safari/605.1.15",
	"Mozilla/5.0 (X11; Linux x86_64; rv:124.0) Gecko/20100101 Firefox/124.0",
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:124.0) Gecko/20100101 Firefox/124.0",
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36 Edg/123.0.0.0",
	"Mozilla/5.0 (iPhone; CPU iPhone OS 17_4 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Mobile/15E148 Safari/604.1",
	"Mozilla/5.0 (Linux; Android 14; SM-G998B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36",
	"curl/8.6.0",
	"Wget/1.21.4",
	"Mozilla/5.0 (compatible; Googlebot/2.1; +http://www.google.com/bot.html)",
}

// pickUserAgent returns the configured/random/default UA in that priority
func pickUserAgent() string {
	if args.UserAgent != "" {
		return args.UserAgent
	}
	if args.RandomAgent {
		return userAgentPool[rand.Intn(len(userAgentPool))]
	}
	return "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/1337.00 (KHTML, like Gecko) Chrome/1337.0.0.0 Safari/1337.00"
}

// newHTTPRequest builds a request with the same headers and cookies used by
// every scan phase. body is nil for the ordinary GET/HEAD/OPTIONS probes and a
// reader only for the WebDAV PROPFIND request document.
func newHTTPRequest(method, url string, body io.Reader) (*http.Request, error) {
	req, err := http.NewRequest(method, url, body)
	if err != nil {
		return nil, err
	}
	req.Header.Set("User-Agent", pickUserAgent())
	for _, h := range args.Headers {
		hs := strings.SplitN(h, ":", 2)
		if len(hs) != 2 {
			return nil, fmt.Errorf("invalid header %q", h)
		}
		name, value := strings.TrimSpace(hs[0]), strings.TrimSpace(hs[1])
		if strings.EqualFold(name, "host") {
			req.Host = value
		} else {
			req.Header.Add(name, value)
		}
	}
	for _, c := range args.Cookies {
		kv := strings.SplitN(c, "=", 2)
		if len(kv) == 2 {
			req.AddCookie(&http.Cookie{Name: strings.TrimSpace(kv[0]), Value: kv[1]})
		}
	}
	return req, nil
}

// executeRequest sends a request and retries transport failures. Response-body
// handling is deliberately left to the caller so status-only candidate-probe probes
// never materialise a large DLL in memory.
func executeRequest(hc *http.Client, st *httpStats, method, url string) (*http.Request, *http.Response, int, error) {
	req, err := newHTTPRequest(method, url, nil)
	if err != nil {
		return nil, nil, 0, err
	}
	return sendWithRetry(hc, st, req)
}

// retryBackoff saturates before multiplication to avoid duration overflow.
func retryBackoff(attempt int, base time.Duration) time.Duration {
	const ceiling = 30 * time.Second
	if base <= 0 {
		base = 500 * time.Millisecond
	}
	for i := 0; i < attempt && base < ceiling; i++ {
		if base >= ceiling/2 {
			return ceiling
		}
		base *= 2
	}
	if base > ceiling {
		return ceiling
	}
	return base
}

// sendWithRetry runs the transport-retry loop on an already-built request, so
// callers that need per-request headers or a body (the WebDAV PROPFIND lift sets
// Depth and sends a prop document) can prepare the request first.
//
// On total failure (every attempt errors) it records the attempt into st itself —
// the request/retry count and wire time spent are real regardless of outcome, and
// every caller below returns immediately on error without ever reaching its own
// recordHTTPStats call, which otherwise left retried-then-failed requests against
// an unreachable host completely invisible in the final "Requests/Retries" summary.
// The success path is unaffected: callers still record their own stats there,
// since only they know the response-body byte count to fold in.
func sendWithRetry(hc *http.Client, st *httpStats, req *http.Request) (*http.Request, *http.Response, int, error) {
	maxAttempts := args.Retries + 1
	if maxAttempts < 1 {
		maxAttempts = 1
	}
	baseDelay := 500 * time.Millisecond
	if args.RetryDelay >= 30000 {
		baseDelay = 30 * time.Second
	} else if args.RetryDelay > 0 {
		baseDelay = time.Duration(args.RetryDelay) * time.Millisecond
	}
	var res *http.Response
	var requestErr error
	attemptCount := 0
	for attempt := 0; attempt < maxAttempts; attempt++ {
		// hc.Do closes req.Body, so a retry would resend with a consumed/closed
		// body — silently breaking the one path that sends one (the WebDAV PROPFIND
		// lift's prop document). Rewind it from GetBody before each re-attempt.
		if attempt > 0 && req.Body != nil {
			if req.GetBody == nil {
				requestErr = fmt.Errorf("cannot retry %s request with a non-rewindable body", req.Method)
				break
			}
			body, err := req.GetBody()
			if err != nil {
				requestErr = fmt.Errorf("rewind %s request body: %w", req.Method, err)
				break
			}
			req.Body = body
		}
		delayRequest()
		attemptCount++
		res, requestErr = hc.Do(req)
		if requestErr == nil {
			log.WithFields(log.Fields{"method": req.Method, "url": req.URL.String(), "status": res.StatusCode}).Trace("fetch()")
			return req, res, attempt, nil
		}
		if req.Context().Err() != nil {
			break
		}
		if attempt+1 < maxAttempts {
			d := retryBackoff(attempt, baseDelay)
			log.WithFields(log.Fields{"err": requestErr}).Trace(fmt.Sprintf("fetch() failed, retrying in %s", d))
			timer := time.NewTimer(d)
			select {
			case <-timer.C:
			case <-req.Context().Done():
				timer.Stop()
				requestErr = req.Context().Err()
			}
			if req.Context().Err() != nil {
				break
			}
		}
	}
	retries := attemptCount - 1
	recordHTTPStats(st, req, nil, retries, 0)
	return req, nil, retries, requestErr
}

// recordHTTPStats folds one HTTP attempt into the running totals. res is nil on a
// total transport failure (every retry errored, see sendWithRetry) — response
// dumping is skipped in that case since there is nothing to dump, but the request
// itself (and the retries spent on it) still counts.
func recordHTTPStats(st *httpStats, req *http.Request, res *http.Response, retries int, bodyBytes int64) {
	st.Lock()
	defer st.Unlock()
	st.requests++
	st.retries += retries
	if dump, err := httputil.DumpRequestOut(req, false); err == nil {
		st.bytesTx += len(dump)
	}
	if res == nil {
		return
	}
	if dump, err := httputil.DumpResponse(res, false); err == nil {
		st.bytesRx += len(dump) + int(bodyBytes)
	}
}

// fetch requests a URL, drains its body using constant memory for connection
// reuse, and returns response metadata. DumpResponse(..., true) used to buffer
// entire DLLs and could exhaust memory on source-disclosure scans.
func fetch(hc *http.Client, st *httpStats, method, url string) (*http.Response, error) {
	req, res, retries, err := executeRequest(hc, st, method, url)
	if err != nil {
		return nil, err
	}
	n, copyErr := io.Copy(io.Discard, res.Body)
	res.Body.Close()
	res.Body = http.NoBody
	recordHTTPStats(st, req, res, retries, n)
	if copyErr != nil {
		log.WithFields(log.Fields{"err": copyErr, "url": url}).Debug("Unable to drain response body")
	}
	return res, nil
}

// fetchBody reads at most limit bytes. It is used only where response content
// participates in matching or disclosure inspection.
func fetchBody(hc *http.Client, st *httpStats, method, url string, limit int64) (*http.Response, []byte, error) {
	req, res, retries, err := executeRequest(hc, st, method, url)
	if err != nil {
		return nil, nil, err
	}
	body, readErr := io.ReadAll(io.LimitReader(res.Body, limit))
	res.Body.Close()
	res.Body = http.NoBody
	recordHTTPStats(st, req, res, retries, int64(len(body)))
	return res, body, readErr
}

// fetchBodyWithHeaders is fetchBody plus per-request headers and an optional
// request body. Only the WebDAV name-lift uses it (Depth:1 + a PROPFIND prop
// document); every other phase keeps the header-free fetchBody path.
func fetchBodyWithHeaders(hc *http.Client, st *httpStats, method, url, reqBody string, limit int64, hdr map[string]string) (*http.Response, []byte, error) {
	var body io.Reader
	if reqBody != "" {
		body = strings.NewReader(reqBody)
	}
	req, err := newHTTPRequest(method, url, body)
	if err != nil {
		return nil, nil, err
	}
	for k, v := range hdr {
		req.Header.Set(k, v)
	}
	req, res, retries, err := sendWithRetry(hc, st, req)
	if err != nil {
		return nil, nil, err
	}
	rb, readErr := io.ReadAll(io.LimitReader(res.Body, limit))
	res.Body.Close()
	res.Body = http.NoBody
	recordHTTPStats(st, req, res, retries, int64(len(rb)))
	return res, rb, readErr
}

// fetchStatus closes the body immediately after headers arrive. This keeps
// status-oracle long-name probing cheap even when the successful candidate is a
// large binary.
func fetchStatus(hc *http.Client, st *httpStats, method, url string) (*http.Response, error) {
	req, res, retries, err := executeRequest(hc, st, method, url)
	if err != nil {
		return nil, err
	}
	res.Body.Close()
	res.Body = http.NoBody
	recordHTTPStats(st, req, res, retries, 0)
	return res, nil
}

// fetchStatusWithHeaders is the constant-memory status path for read-only
// probes whose semantics depend on request headers. The Allow/COPY oracle uses
// PROPFIND with Depth: 0 but never needs the response body.
func fetchStatusWithHeaders(hc *http.Client, st *httpStats, method, url string, hdr map[string]string) (*http.Response, error) {
	req, err := newHTTPRequest(method, url, nil)
	if err != nil {
		return nil, err
	}
	for k, v := range hdr {
		req.Header.Set(k, v)
	}
	req, res, retries, err := sendWithRetry(hc, st, req)
	if err != nil {
		return nil, err
	}
	res.Body.Close()
	res.Body = http.NoBody
	recordHTTPStats(st, req, res, retries, 0)
	return res, nil
}

// buildClient builds the configured *http.Client honouring proxy/TLS/HTTP2 flags
func buildClient() *http.Client {
	// Reuse connections aggressively. shortscan hammers a single host, so the
	// stdlib default of MaxIdleConnsPerHost=2 forces a fresh TCP (+TLS) handshake
	// for almost every concurrent probe — the dominant wall-clock cost on TLS
	// targets. Sizing the idle pool to the concurrency level keeps sockets warm.
	// The requests are byte-for-byte identical; only their transport is reused, so
	// results do not change — this is pure latency, not coverage.
	idlePerHost := args.Concurrency
	if idlePerHost < 1 {
		idlePerHost = 1
	}
	tr := &http.Transport{
		TLSClientConfig: &tls.Config{
			InsecureSkipVerify: args.Insecure,
			Renegotiation:      tls.RenegotiateOnceAsClient,
			MinVersion:         tlsMinVersion(args.TLSMin),
		},
		Proxy:             http.ProxyFromEnvironment,
		ForceAttemptHTTP2: args.HTTP2,
		// MaxIdleConnsPerHost is the meaningful cap (sized to -c above); MaxIdleConns is
		// the GLOBAL idle pool shared across every concurrently-scanned host. A single
		// *http.Client is built once and reused for the whole run, including under
		// --parallel (default 10 hosts at once) — a fixed idlePerHost*2 global cap
		// silently evicted most hosts' connections under the default bulk-scan
		// invocation, reintroducing the per-probe handshake cost this pool exists to
		// avoid. 0 means unlimited globally; MaxIdleConnsPerHost still bounds each host.
		MaxIdleConns:          0,
		MaxIdleConnsPerHost:   idlePerHost,
		IdleConnTimeout:       90 * time.Second,
		TLSHandshakeTimeout:   time.Duration(args.Timeout) * time.Second,
		ExpectContinueTimeout: 1 * time.Second,
	}
	if args.Proxy != "" {
		pu, err := nurl.Parse(args.Proxy)
		if err != nil {
			log.WithFields(log.Fields{"err": err, "proxy": args.Proxy}).Fatal("Invalid --proxy URL")
		}
		if args.ProxyAuth != "" {
			parts := strings.SplitN(args.ProxyAuth, ":", 2)
			if len(parts) == 2 {
				pu.User = nurl.UserPassword(parts[0], parts[1])
			}
		}
		tr.Proxy = http.ProxyURL(pu)
		log.WithFields(log.Fields{"proxy": pu.Redacted()}).Info("Using proxy")
	}
	return &http.Client{
		Timeout:       time.Duration(args.Timeout) * time.Second,
		Transport:     tr,
		CheckRedirect: func(req *http.Request, via []*http.Request) error { return http.ErrUseLastResponse },
	}
}

// tlsMinVersion translates "1.0".."1.3" into a tls.Version constant
func tlsMinVersion(v string) uint16 {
	switch v {
	case "1.1":
		return tls.VersionTLS11
	case "1.2":
		return tls.VersionTLS12
	case "1.3":
		return tls.VersionTLS13
	default:
		return tls.VersionTLS10
	}
}
