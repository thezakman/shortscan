package shortscan

import (
	"bufio"
	"context"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"embed"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"math/rand"
	"net/http"
	"net/http/httputil"
	nurl "net/url"
	"os"
	"path"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/alexflint/go-arg"
	"github.com/fatih/color"
	"github.com/thezakman/shortscan/pkg/levenshtein"
	"github.com/thezakman/shortscan/pkg/maths"
	"github.com/thezakman/shortscan/pkg/shortutil"
	log "github.com/sirupsen/logrus"
)

// base types, stats and wordlist records

type baseRequest struct {
	url   string
	file  string
	tilde string
	ext   string
}

type httpStats struct {
	sync.Mutex
	bytesTx  int
	bytesRx  int
	requests int
	retries  int
}

type markers struct {
	statusPos int
	statusNeg int
}

type distances struct {
	distance float32
	body     string
}

type wordlistRecord struct {
	checksums   string
	filename    string
	extension   string
	filename83  string
	extension83 string
}

type wordlistConfig struct {
	wordlist  []wordlistRecord
	isRainbow bool
	sync.Mutex
}

type attackConfig struct {
	method            string
	suffix            string
	override          string // non-empty => tamper via X-HTTP-Method-Override header chain, value is wire verb
	tildes            []string
	fileChars         map[string]string
	extChars          map[string]string
	foundFiles        map[string]struct{}
	foundDirectories  map[string]struct{}
	wordlist          wordlistConfig
	distanceMutex     sync.Mutex
	autocompleteMutex sync.Mutex
}

// hashBucket stores the SHA-256 fingerprints and content-length band for
// "known-miss" responses per extension + status code.  Used by the `hash`
// autocomplete mode as a cheap, stable alternative to Levenshtein.
type hashBucket struct {
	sums      map[string]struct{}
	minLen    int
	maxLen    int
	populated bool
}

var hashCache map[string]map[int]*hashBucket
var hashMutex sync.Mutex

// iisFingerprint captures what we were able to glean from banner headers.
// Populated once per host during the probe stage; used by prioritiseProbeOrder
// to front-load the verb/suffix combinations most likely to work.
type iisFingerprint struct {
	server        string
	isIIS         bool
	majorVersion  int
	aspNet        bool
	aspNetCore    bool
	poweredByPHP  bool
	kestrelFront  bool
	hasWAFMarkers bool
}

// rateLimiter is a tiny token-bucket shaped around time.Ticker.  Built to avoid
// an external dependency; a miss on Take() blocks until the next tick.  The
// adaptive fields are nudged by fetch() when it sees 429/503/Retry-After.
type rateLimiter struct {
	mu       sync.Mutex
	interval time.Duration   // minimum gap between requests (0 = disabled)
	next     time.Time       // earliest time the next request may run
	penalty  time.Duration   // stacked backoff from adaptive throttling
	adaptive bool
	enabled  bool
}

func newRateLimiter(rps float64, adaptive bool) *rateLimiter {
	rl := &rateLimiter{adaptive: adaptive}
	if rps > 0 {
		rl.interval = time.Duration(float64(time.Second) / rps)
		rl.enabled = true
	} else if adaptive {
		rl.enabled = true
	}
	return rl
}

// Wait blocks until the caller is allowed to issue the next request.
func (rl *rateLimiter) Wait(ctx context.Context) error {
	if rl == nil || !rl.enabled {
		return nil
	}
	rl.mu.Lock()
	now := time.Now()
	var sleepFor time.Duration
	if rl.interval > 0 {
		if now.Before(rl.next) {
			sleepFor = rl.next.Sub(now)
		}
		rl.next = now.Add(sleepFor).Add(rl.interval)
	}
	if rl.penalty > 0 {
		sleepFor += rl.penalty
		rl.next = rl.next.Add(rl.penalty)
		// Bleed penalty down: half-life ~1s of clock time.
		rl.penalty = rl.penalty / 2
		if rl.penalty < 10*time.Millisecond {
			rl.penalty = 0
		}
	}
	rl.mu.Unlock()
	if sleepFor <= 0 {
		return nil
	}
	select {
	case <-time.After(sleepFor):
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// Throttle increases the backoff, typically in response to 429/503/Retry-After.
func (rl *rateLimiter) Throttle(d time.Duration) {
	if rl == nil || !rl.adaptive || d <= 0 {
		return
	}
	rl.mu.Lock()
	defer rl.mu.Unlock()
	// Clamp so a badly-formed Retry-After can't stall the scan forever.
	if d > 30*time.Second {
		d = 30 * time.Second
	}
	rl.penalty += d
	if rl.penalty > 60*time.Second {
		rl.penalty = 60 * time.Second
	}
}

// checkpointWriter persists discovered hits and directories to a newline-
// delimited JSON file.  On startup we replay the file so scans survive
// interruption.  Append-only + line-flushed = crash-safe enough for our needs.
type checkpointWriter struct {
	mu   sync.Mutex
	file *os.File
}

type checkpointRecord struct {
	Type     string `json:"type"`
	URL      string `json:"url,omitempty"`
	FullPath string `json:"fullpath,omitempty"`
	IsDir    bool   `json:"isdir,omitempty"`
}

func newCheckpointWriter(path string) (*checkpointWriter, map[string]map[string]bool, map[string]struct{}, error) {
	// Replay existing state (hits per-URL + visited set) before we truncate nothing.
	state := make(map[string]map[string]bool) // baseURL -> fullpath -> isDir
	visited := make(map[string]struct{})
	if fh, err := os.Open(path); err == nil {
		sc := bufio.NewScanner(fh)
		sc.Buffer(make([]byte, 0, 64*1024), 1024*1024)
		for sc.Scan() {
			var r checkpointRecord
			if json.Unmarshal(sc.Bytes(), &r) != nil {
				continue
			}
			switch r.Type {
			case "visit":
				if r.URL != "" {
					visited[r.URL] = struct{}{}
				}
			case "hit":
				if r.URL != "" && r.FullPath != "" {
					if _, ok := state[r.URL]; !ok {
						state[r.URL] = make(map[string]bool)
					}
					state[r.URL][r.FullPath] = r.IsDir
				}
			}
		}
		fh.Close()
	}
	fh, err := os.OpenFile(path, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		return nil, nil, nil, err
	}
	return &checkpointWriter{file: fh}, state, visited, nil
}

func (c *checkpointWriter) write(r checkpointRecord) {
	if c == nil {
		return
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	b, err := json.Marshal(r)
	if err != nil {
		return
	}
	c.file.Write(b)
	c.file.Write([]byte("\n"))
	c.file.Sync()
}

func (c *checkpointWriter) close() {
	if c != nil && c.file != nil {
		c.file.Close()
	}
}

// Reserved DOS device names -- still refuse to be opened by the Windows I/O
// manager, which is why they routinely drop an ASP.NET stack trace that
// exposes the physical root path.
var reservedNames = []string{
	"CON", "PRN", "AUX", "NUL",
	"COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7", "COM8", "COM9",
	"LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9",
}

type resultOutput struct {
	Type       string  `json:"type"`
	FullMatch  bool    `json:"fullmatch"`
	BaseUrl    string  `json:"baseurl"`
	File       string  `json:"shortfile"`
	Ext        string  `json:"shortext"`
	Tilde      string  `json:"shorttilde"`
	Partname   string  `json:"partname"`
	Fullname   string  `json:"fullname"`
	Confidence float64 `json:"confidence,omitempty"`
	Source     string  `json:"source,omitempty"` // "wordlist", "dechecksum", "partial", ""
}

type statusOutput struct {
	Type       string `json:"type"`
	Url        string `json:"url"`
	Server     string `json:"server"`
	Vulnerable bool   `json:"vulnerable"`
}

type statsOutput struct {
	Type          string `json:"type"`
	Requests      int    `json:"requests"`
	Retries       int    `json:"retries"`
	SentBytes     int    `json:"sentbytes"`
	ReceivedBytes int    `json:"receivedbytes"`
}

// Version, rainbow table magic, default character set
const version = "0.9.4"
const rainbowMagic = "#SHORTSCAN#"
const alphanum = "JFKGOTMYVHSPCANDXLRWEBQUIZ8549176320"

// Standard headers + IIS DEBUG, ordered roughly by frequency and probable response time
// https://www.iana.org/assignments/http-methods/http-methods.xhtml#methods
var httpMethods = [...]string{
	"OPTIONS", "HEAD", "TRACE", "DEBUG", "GET", "POST", "PUT", "PATCH", "DELETE", "ACL",
	"BASELINE-CONTROL", "BIND", "CHECKIN", "CHECKOUT", "CONNECT", "COPY", "LABEL", "LINK",
	"LOCK", "MERGE", "MKACTIVITY", "MKCALENDAR", "MKCOL", "MKREDIRECTREF", "MKWORKSPACE",
	"MOVE", "ORDERPATCH", "PRI", "PROPFIND", "PROPPATCH", "REBIND", "REPORT", "SEARCH",
	"UNBIND", "UNCHECKOUT", "UNLINK", "UNLOCK", "UPDATE", "UPDATEREDIRECTREF", "VERSION-CONTROL",
}

// Path suffixes to try. Includes modern IIS/ASP.NET handler bypass variants that
// tend to survive when the standard `/` and `/.aspx` suffixes are filtered by a
// WAF or URL-normalisation layer. Extras such as "::$DATA", backslash terminator
// and a trailing dot/space exploit well-known IIS request-parser quirks.
var pathSuffixes = [...]string{
	"/", "",
	"/.aspx", "?aspxerrorpath=/", "/.aspx?aspxerrorpath=/",
	"/.asmx", "/.vb",
	"/.ashx", "/.svc", "/.rem", "/.soap",
	"/a.aspx", "/a.asmx", "/a.ashx",
	"/web.config", "/global.asax",
	"\\", "::$DATA", ".", "%20",
}

// Embed the default wordlist
//
//go:embed resources/wordlist.txt
var defaultWordlist embed.FS

// Caches and regexes
var statusCache map[string]map[int]struct{}
var distanceCache map[string]map[int]distances
var checksumRegex *regexp.Regexp

// Package-level singletons wired up in Run().  These are read from fetch(),
// enumerate(), Scan() etc.; keeping them here avoids threading yet another
// struct through every call-site.
var (
	globalLimiter    *rateLimiter
	globalCheckpoint *checkpointWriter
	globalFingerprint atomic.Value // iisFingerprint -- set once per host probe
)

// Command-line arguments and help
type arguments struct {
	Urls             []string `arg:"positional" help:"url to scan (multiple URLs can be specified)" placeholder:"URL"`
	List             string   `arg:"--list,-l" help:"file containing list of URLs to scan" placeholder:"FILE"`
	Wordlist         string   `arg:"-w" help:"combined wordlist + rainbow table generated with shortutil" placeholder:"FILE"`
	Headers          []string `arg:"--header,-H,separate" help:"header to send with each request (use multiple times for multiple headers)"`
	Concurrency      int      `arg:"-c" help:"number of requests to make at once" default:"20"`
	Timeout          int      `arg:"-t" help:"per-request timeout in seconds" placeholder:"SECONDS" default:"10"`
	Output           string   `arg:"-o" help:"output format (human = human readable; json = JSON; ndjson = line-delimited JSON)" placeholder:"format" default:"human"`
	Verbosity        int      `arg:"-v" help:"how much noise to make (0 = quiet; 1 = debug; 2 = trace)" default:"0"`
	FullUrl          bool     `arg:"-F" help:"display the full URL for confirmed files rather than just the filename" default:"false"`
	NoRecurse        bool     `arg:"-n" help:"don't detect and recurse into subdirectories (disabled when autocomplete is disabled)" default:"false"`
	Stabilise        bool     `arg:"-s" help:"attempt to get coherent autocomplete results from an unstable server (generates more requests)" default:"false"`
	Patience         int      `arg:"-p" help:"patience level when determining vulnerability (0 = patient; 1 = very patient)" placeholder:"LEVEL" default:"0"`
	Characters       string   `arg:"-C" help:"filename characters to enumerate" default:"JFKGOTMYVHSPCANDXLRWEBQUIZ8549176320-_()&'!#$%@^{}~"`
	Autocomplete     string   `arg:"-a" help:"autocomplete detection mode (auto = autoselect; method = HTTP method magic; status = HTTP status; distance = Levenshtein distance; hash = SHA-256 + length; none = disable)" placeholder:"mode" default:"auto"`
	IsVuln           bool     `arg:"-V" help:"bail after determining whether the service is vulnerable" default:"false"`
	Index            bool     `arg:"-i" help:"test ::$INDEX_ALLOCATION and :$i30:$INDEX_ALLOCATION"`
	BackwardsRecurse bool     `arg:"--backwards-recurse,-r" help:"perform regressive scanning on parent directories" default:"false"`

	// Network / evasion
	Proxy     string `arg:"--proxy" help:"upstream HTTP/HTTPS proxy (e.g. http://127.0.0.1:8080 for Burp/ZAP)" placeholder:"URL"`
	CA        string `arg:"--ca" help:"PEM file with extra CAs to trust" placeholder:"FILE"`
	Insecure  bool   `arg:"--insecure" help:"skip TLS certificate verification" default:"true"`
	UserAgent string `arg:"--user-agent,-U" help:"User-Agent header to send" placeholder:"UA"`

	// Rate limiting
	RPS      float64 `arg:"--rps" help:"hard cap of requests per second across all workers (0 = unlimited)" default:"0"`
	Adaptive bool    `arg:"--adaptive" help:"auto-throttle on 429/503/Retry-After responses" default:"true"`

	// Enumeration breadth
	MaxTilde  int  `arg:"--max-tilde" help:"highest tilde collision index to probe (1-9)" placeholder:"N" default:"4"`
	DeepTilde bool `arg:"--deep-tilde" help:"probe tilde collisions up to ~9 (shortcut for --max-tilde=9)" default:"false"`

	// Verb tampering
	VerbOverride bool `arg:"--verb-override" help:"retry blocked verbs via X-HTTP-Method-Override header chain" default:"false"`

	// Persistence
	Checkpoint string `arg:"--checkpoint" help:"append discovered hits / directories to this NDJSON file and resume from it on next run" placeholder:"FILE"`

	// Extra probes
	Reserved bool `arg:"--reserved" help:"after detection, probe Windows reserved names (CON, PRN, AUX, NUL, COM1-9, LPT1-9)" default:"false"`
}

func (arguments) Version() string {
	return getBanner()
}

var args arguments

// getBanner returns the main banner
func getBanner() string {
	return color.New(color.FgWhite, color.Bold).Sprint("🧩 Shortscan v" + version) +
		" · " + color.New(color.FgBlue, color.Bold).Sprint("an IIS short filename enumeration ") + color.New(color.FgWhite).Sprint("· (bitquark & TheZakMan)")
}

// pathEscape returns an escaped URL with spaces encoded as %20 rather than + (which can cause odd behaviour from IIS in some modes)
func pathEscape(url string) string {
	return strings.Replace(nurl.QueryEscape(url), "+", "%20", -1)
}

// replaceBinALLOCATION replaces bin::$INDEX_ALLOCATION with a valid path to download .DLL
func replaceBinALLOCATION(url string) string {
	u, _ := nurl.Parse(url)
	segments := strings.Split(strings.Trim(u.Path, "/"), "/")
	lastSegment := segments[len(segments)-1]

	if lastSegment == "bin::$INDEX_ALLOCATION" {
		newPath := strings.Join(segments[:len(segments)-1], "/")
		if newPath == "" {
			newPath = "(S(x))/b/(S(x))in/"
		} else {
			newPath += "/(S(x))/b/(S(x))in/"
		}
		url = u.Scheme + "://" + u.Host + "/" + newPath
	}
	return url
}

// fetch requests the given URL and returns an HTTP response object, handling retries gracefully
func fetch(hc *http.Client, st *httpStats, method string, url string) (*http.Response, error) {
	return fetchWithOverride(hc, st, method, "", url)
}

// fetchWithOverride extends fetch() with optional verb tampering: when
// `override` is non-empty, the wire-verb becomes `method` and the real verb is
// transmitted via the X-HTTP-Method-Override header chain.  Several WAFs drop
// uncommon verbs outright but forward the override header unchanged.
func fetchWithOverride(hc *http.Client, st *httpStats, method string, override string, url string) (*http.Response, error) {

	// If the caller asked for verb-override, send the wire verb instead and
	// smuggle the real verb via three headers (different stacks look at
	// different header names).
	wireMethod := method
	if override != "" {
		wireMethod = override
	}
	req, err := http.NewRequest(wireMethod, url, nil)
	if err != nil {
		log.WithFields(log.Fields{"err": err}).Fatal("Unable to create request object")
	}

	// Default user agent (overridable via --user-agent)
	ua := args.UserAgent
	if ua == "" {
		ua = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/1337.00 (KHTML, like Gecko) Chrome/1337.0.0.0 Safari/1337.00"
	}
	req.Header.Set("User-Agent", ua)

	if override != "" {
		req.Header.Set("X-HTTP-Method-Override", method)
		req.Header.Set("X-HTTP-Method", method)
		req.Header.Set("X-Method-Override", method)
	}

	// Loop through custom headers
	for _, h := range args.Headers {
		hs := strings.SplitN(h, ":", 2)
		if len(hs) != 2 {
			log.WithFields(log.Fields{"header": h}).Fatal("Invalid header")
		}
		h, v := strings.Trim(hs[0], " "), strings.Trim(hs[1], " ")
		if strings.ToLower(h) == "host" {
			req.Host = v
		} else {
			req.Header.Add(h, v)
		}
	}

	// Wait for the shared rate limiter (if any) before putting anything on the wire.
	if globalLimiter != nil {
		_ = globalLimiter.Wait(context.Background())
	}

	// Request loop
	var t int
	var rerr error
	var res *http.Response
	for t = 0; t < 4; t++ {
		res, rerr = hc.Do(req)
		if rerr == nil {
			break
		}
		d := time.Duration(t*2) * time.Second
		log.WithFields(log.Fields{"err": rerr}).Trace(fmt.Sprintf("fetch() failed, retrying in %s", d))
		time.Sleep(d)
	}

	if res == nil {
		return nil, rerr
	}

	log.WithFields(log.Fields{"method": wireMethod, "override": override, "url": url, "status": res.StatusCode}).Trace("fetch()")

	// Adaptive rate limiting: on 429/503/509 honour Retry-After and nudge the shared limiter.
	if globalLimiter != nil && (res.StatusCode == 429 || res.StatusCode == 503 || res.StatusCode == 509) {
		backoff := 250 * time.Millisecond
		if ra := res.Header.Get("Retry-After"); ra != "" {
			if secs, err := strconv.Atoi(ra); err == nil {
				backoff = time.Duration(secs) * time.Second
			} else if ts, err := http.ParseTime(ra); err == nil {
				if d := time.Until(ts); d > 0 {
					backoff = d
				}
			}
		}
		globalLimiter.Throttle(backoff)
		log.WithFields(log.Fields{"status": res.StatusCode, "backoff": backoff}).Debug("Rate-limit signal detected, throttling")
	}

	// Update request stats
	st.Lock()
	st.requests++
	st.retries += t
	if r, err := httputil.DumpRequestOut(req, true); err == nil {
		st.bytesTx += len(r)
	} else {
		log.WithFields(log.Fields{"err": err}).Fatal("Error dumping request")
	}
	if r, err := httputil.DumpResponse(res, true); err == nil {
		st.bytesRx += len(r)
	} else {
		log.WithFields(log.Fields{"err": err}).Fatal("Error dumping response")
	}
	st.Unlock()

	// Close the response body to allow connection reuse
	res.Body.Close()

	return res, nil
}

// fetchFromAttack is a thin helper that funnels the ac.method + ac.override
// combination through fetchWithOverride.  Used by enumerate() and friends so
// they don't have to know whether verb-tampering is in use.
func fetchFromAttack(hc *http.Client, st *httpStats, ac *attackConfig, url string) (*http.Response, error) {
	return fetchWithOverride(hc, st, ac.method, ac.override, url)
}

// enumerate builds and fetches candidate short name URLs using recursion
func enumerate(sem chan struct{}, wg *sync.WaitGroup, hc *http.Client, st *httpStats, ac *attackConfig, mk markers, br baseRequest) {

	// Determine if in extension enumeration mode
	extMode := len(br.ext) > 0

	// Select the character map to use
	var chars string
	if extMode {
		chars = ac.extChars[br.tilde]
	} else {
		chars = ac.fileChars[br.tilde]
	}

	// Loop through characters
	for _, char := range chars {
		wg.Add(1)
		go func(sem chan struct{}, wg *sync.WaitGroup, hc *http.Client, ac *attackConfig, mk markers, br baseRequest, char string) {
			sem <- struct{}{}
			defer func() {
				<-sem
				wg.Done()
			}()

			// Workaround for an IIS bug with "%" followed by two hex digits
			if char == "%" {
				var x, y int
				if extMode {
					x, y = len(br.ext), 1
				} else {
					x, y = len(br.file), 4
				}
				for i := 0; i < 2 && x < y; i++ {
					char += "?"
				}
			}

			// Append the next character and build the candidate URL
			var url string
			if extMode {
				br.ext += char
				url = br.url + pathEscape(br.file) + br.tilde + pathEscape(br.ext) + "*" + ac.suffix
			} else {
				br.file += char
				url = br.url + pathEscape(br.file) + "*" + br.tilde + "*" + pathEscape(br.ext) + ac.suffix
			}

			// Check if this looks like a hit
			res, err := fetchFromAttack(hc, st, ac, url)
			if err == nil && res.StatusCode == mk.statusPos {
				// Check if the full file part is reached
				res, err := fetchFromAttack(hc, st, ac, br.url+pathEscape(br.file)+br.tilde+"*"+pathEscape(br.ext)+ac.suffix)
				if err == nil && res.StatusCode == mk.statusPos {
					res, err := fetchFromAttack(hc, st, ac, br.url+pathEscape(br.file)+br.tilde+pathEscape(br.ext)+ac.suffix)
					if err == nil && res.StatusCode != mk.statusNeg {
						var fnr, method, source string
						confidence := 0.5 // partial short-name, no full-name resolution yet
						if args.Autocomplete != "none" {
							var fnc []wordlistRecord
							fromChecksum := make(map[string]bool)
							if cm := ac.wordlist.isRainbow && checksumRegex.MatchString(br.file); cm {
								fnc = autodechecksum(ac, br)
								for _, r := range fnc {
									fromChecksum[r.filename+r.extension] = true
								}
							}
							fnc = append(fnc, autocomplete(ac, br)...)
							if args.Autocomplete == "method" {
								method = "_"
							} else {
								method = "GET"
							}
							for _, c := range fnc {
								func() {
									ac.autocompleteMutex.Lock()
									defer ac.autocompleteMutex.Unlock()
									candidatePath := pathEscape(c.filename + c.extension)
									if _, ok := ac.foundFiles[candidatePath]; ok {
										return
									}
									if strings.ToLower(br.ext) == ".dll" {
										br.url = replaceBinALLOCATION(br.url)
									}
									res, err := fetch(hc, st, method, br.url+candidatePath)
									if err != nil {
										log.WithFields(log.Fields{"err": err, "method": method, "url": br.url + candidatePath}).Info("Existence check error")
										return
									}
									switch args.Autocomplete {
									case "method":
										if res.StatusCode == 405 {
											fnr = candidatePath
										}
									case "status":
										ss := getStatuses(c, br, hc, st)
										if _, e := ss[res.StatusCode]; !e {
											fnr = candidatePath
										}
									case "distance":
										dists := getDistances(c, br, hc, st, ac)
										if dists[res.StatusCode] == (distances{}) {
											log.WithFields(log.Fields{"url": br.url + candidatePath, "status": res.StatusCode}).Info("Autocomplete got a status code hit")
											fnr = candidatePath
										} else {
											b := make([]byte, 1024)
											res.Body.Read(b)
											body, sbody := string(b), dists[res.StatusCode].body
											lp := float32(levenshtein.Distance(sbody, body)) / float32(maths.Max(len(sbody), len(body)))
											if d := lp - dists[res.StatusCode].distance; d > 0.1 {
												log.WithFields(log.Fields{"url": br.url + candidatePath, "distance": lp, "delta": d}).Info("Autocomplete got a distance hit")
												fnr = candidatePath
											}
										}
									case "hash":
										if hashHit(c, br, hc, st, res) {
											log.WithFields(log.Fields{"url": br.url + candidatePath, "status": res.StatusCode}).Info("Autocomplete got a hash/length hit")
											fnr = candidatePath
										}
									default:
										log.Fatal("What are you doing here?")
									}
									if fnr != "" {
										ac.foundFiles[fnr] = struct{}{}
										if fromChecksum[c.filename+c.extension] {
											source = "dechecksum"
											confidence = 0.85
										} else {
											source = "wordlist"
											confidence = 1.0
										}
										if !args.NoRecurse {
											res, err := fetch(hc, st, "HEAD", br.url+fnr)
											if err != nil {
												log.WithFields(log.Fields{"err": err, "method": "HEAD", "url": br.url + fnr}).Info("Directory recursion check error")
											} else {
												if loc := res.Header.Get("Location"); strings.HasSuffix(strings.ToLower(loc), "/"+strings.ToLower(fnr)+"/") {
													ac.foundDirectories[fnr] = struct{}{}
												}
											}
										}
									}
								}()
								if fnr != "" {
									break
								}
							}
						}
						fn, fe := br.file, br.ext
						if len(fn) >= 6 {
							fn = fn + "?"
						}
						if len(fe) >= 4 {
							fe = fe + "?"
						}
						if source == "" && fnr == "" {
							source = "partial"
						}
						if args.Output == "human" {
							var fp, ff string
							if fnr != "" {
								fp = color.HiBlackString(fn + fe)
								if args.FullUrl {
									ff = color.GreenString(br.url) + color.HiGreenString(pathEscape(strings.ToLower(fnr)))
								} else {
									ff = color.HiGreenString(fnr)
								}
							} else {
								if len(br.file) < 6 {
									fn = color.GreenString(fn)
								}
								if len(br.ext) < 4 {
									fe = color.GreenString(fe)
								}
								fp = strings.Replace(fn+fe, "?", color.HiBlackString("?"), -1)
							}
							printHuman(fmt.Sprintf("%-20s %-28s %s", br.file+br.tilde+br.ext, fp, ff))
						} else {
							o := resultOutput{
								Type:       "result",
								FullMatch:  fnr != "",
								BaseUrl:    br.url,
								File:       br.file,
								Tilde:      br.tilde,
								Ext:        br.ext,
								Partname:   fn + fe,
								Fullname:   fnr,
								Confidence: confidence,
								Source:     source,
							}
							printJSON(o)
						}
						if globalCheckpoint != nil {
							globalCheckpoint.write(checkpointRecord{
								Type:     "hit",
								URL:      br.url,
								FullPath: fnr,
								IsDir:    fnr != "" && func() bool { _, ok := ac.foundDirectories[fnr]; return ok }(),
							})
						}
					} else if err == nil && len(br.ext) > 0 {
						log.WithFields(log.Fields{"status": res.StatusCode, "statusNeg": mk.statusNeg, "filename": br.file + br.tilde + br.ext + ac.suffix}).
							Debug("Possible hit, but status is the same as a negative match")
					}
					if len(br.ext) == 0 {
						nr := br
						nr.ext = "."
						enumerate(sem, wg, hc, st, ac, mk, nr)
					}
				}
				if (extMode && len(br.ext) < 4) || (!extMode && len(br.file) < 6) {
					var url string
					if extMode {
						url = br.url + pathEscape(br.file) + br.tilde + pathEscape(br.ext) + "%3f*" + ac.suffix
					} else {
						url = br.url + pathEscape(br.file) + "%3f*" + br.tilde + "*" + pathEscape(br.ext) + ac.suffix
					}
					res, err = fetchFromAttack(hc, st, ac, url)
					if err == nil && res.StatusCode != mk.statusNeg {
						enumerate(sem, wg, hc, st, ac, mk, br)
					}
				}
			}
		}(sem, wg, hc, ac, mk, br, string(char))
	}
}

// testIndexAllocations tests special paths such as ::$INDEX_ALLOCATION
func testIndexAllocations(urls []string, hc *http.Client, st *httpStats, wc wordlistConfig, mk markers) {
	paths := []string{"::$INDEX_ALLOCATION"}
	for _, url := range urls {
		// Ensure URL has proper format and add /bin path
		url = strings.TrimSuffix(url, "/")
		
		// Parse URL to check if it has a path
		parsedURL, err := nurl.Parse(url)
		if err != nil {
			log.WithFields(log.Fields{"url": url, "error": err}).Error("Unable to parse URL")
			continue
		}
		
		// If URL has no path or only "/", add /bin
		if parsedURL.Path == "" || parsedURL.Path == "/" {
			url = url + "/bin"
		}
		
		for _, p := range paths {
			modifiedURL := url + p
			Scan([]string{modifiedURL}, hc, st, wc, mk, make(map[string]struct{}))
		}
	}
}

// autocomplete returns a list of possible full filenames for a given tilde filename
func autocomplete(ac *attackConfig, br baseRequest) []wordlistRecord {
	fs := make(map[string]wordlistRecord)
	ch := make(chan wordlistRecord, 1024)
	go getWordlist(ch, ac)
	for record := range ch {
		if br.file == record.filename83 && br.ext[maths.Min(len(br.ext), 1):] == record.extension83 {
			fs[record.filename+record.extension] = record
		}
	}
	f := make([]wordlistRecord, 0, len(fs))
	for _, v := range fs {
		f = append(f, v)
	}
	if len(f) > 0 {
		log.WithFields(log.Fields{"file": br.file, "ext": br.ext, "count": len(f)}).Info("Autocomplete found candidates")
		log.WithFields(log.Fields{"candidates": f}).Trace("Autocomplete candidates")
	}
	return f
}

// autodechecksum attempts to reconstruct Windows checksummed filenames (e.g. A5FAB~1.HTM)
func autodechecksum(ac *attackConfig, br baseRequest) []wordlistRecord {
	l := 2 - (6 - len(br.file))
	prefix, checksum := br.file[:l], br.file[l:]
	log.WithFields(log.Fields{"file": br.file, "prefix": prefix, "checksum": checksum}).Info("Possible checksummed alias")
	fs := make(map[string]wordlistRecord)
	ch := make(chan wordlistRecord, 1024)
	go getWordlist(ch, ac)
	for record := range ch {
		for i := 0; i < len(record.checksums); i += 4 {
			c := record.checksums[i : i+4]
			if c == checksum && strings.HasPrefix(strings.ToUpper(record.filename), prefix) && strings.HasPrefix(strings.ToUpper(record.extension), br.ext) {
				fs[record.filename+record.extension] = record
			}
		}
	}
	f := make([]wordlistRecord, 0, len(fs))
	for _, v := range fs {
		f = append(f, v)
	}
	if len(f) > 1 {
		log.WithFields(log.Fields{"file": br.file, "ext": br.ext, "count": len(f)}).Info("Dechecksum found candidates")
		log.WithFields(log.Fields{"candidates": f}).Trace("Dechecksum candidates")
	}
	return f
}

// getStatuses fetches non-existent URLs and returns a set of response statuses
func getStatuses(c wordlistRecord, br baseRequest, hc *http.Client, st *httpStats) map[int]struct{} {
	if len(statusCache[c.extension]) > 0 {
		return statusCache[c.extension]
	}
	l := 2
	if args.Stabilise {
		l = 12
	}
	statuses := make(map[int]struct{}, l)
	for i := 0; i < l; i++ {
		p := randPath(rand.Intn(4)+8, 0, alphanum) + c.extension
		if res, err := fetch(hc, st, "GET", br.url+p); err == nil {
			statuses[res.StatusCode] = struct{}{}
		}
	}
	log.WithFields(log.Fields{"extension": c.extension, "statuses": statuses}).Info("Got non-existent file statuses")
	statusCache[c.extension] = statuses
	return statuses
}

// getDistances calculates response distances using Levenshtein
func getDistances(c wordlistRecord, br baseRequest, hc *http.Client, st *httpStats, ac *attackConfig) map[int]distances {
	ac.distanceMutex.Lock()
	defer ac.distanceMutex.Unlock()
	if len(distanceCache[c.extension]) > 0 {
		return distanceCache[c.extension]
	}
	log.WithFields(log.Fields{"url": br.url, "extension": c.extension}).Info("Sampling responses for Levenshtein distance calculation")
	l := 4
	if args.Stabilise {
		l = 24
	}
	bodies := make(map[int][]string, l)
	highdist := make(map[int]float32, l)
	dists := make(map[int]distances)
	var p string
	for i := 0; i < l; i++ {
		p = randPath(rand.Intn(4)+8, 0, alphanum) + c.extension
		if res, err := fetch(hc, st, "GET", br.url+p); err == nil {
			b := make([]byte, 1024)
			res.Body.Read(b)
			body := string(b)
			for j := 0; j < len(bodies[res.StatusCode])-1; j++ {
				ld := levenshtein.Distance(bodies[res.StatusCode][j], body)
				lp := float32(ld) / float32(maths.Max(len(bodies[res.StatusCode][j]), len(body)))
				if dists[res.StatusCode] == (distances{}) || lp > highdist[res.StatusCode] {
					dists[res.StatusCode] = distances{lp, body}
					highdist[res.StatusCode] = lp
				}
			}
			bodies[res.StatusCode] = append(bodies[res.StatusCode], body)
		}
	}
	for s, d := range dists {
		log.WithFields(log.Fields{"extension": c.extension, "status": s, "distance": d.distance}).Info("Calculated Levenshtein distance")
	}
	distanceCache[c.extension] = dists
	return dists
}

// getWordlist returns wordlist entries
func getWordlist(ch chan wordlistRecord, ac *attackConfig) {
	ac.wordlist.Lock()
	for _, record := range ac.wordlist.wordlist {
		ch <- record
	}
	ac.wordlist.Unlock()
	close(ch)
}

// randPath returns a random path built with the provided characters
func randPath(l int, d int, chars string) string {
	c := len(chars)
	b := make([]byte, l)
	for i := range b {
		b[i] = chars[rand.Intn(c)]
	}
	for i := 0; i < d; i++ {
		b[rand.Intn(l)] = '.'
	}
	return pathEscape(string(b))
}

// printHuman prints human-readable output if enabled
func printHuman(s ...any) {
	if args.Output == "human" {
		fmt.Println(s...)
	}
}

// printJSON prints JSON formatted output if enabled.  Both "json" and "ndjson"
// emit one JSON document per line; the ndjson mode additionally flushes stdout
// after each line so downstream tools (jq, triage scripts) see results live.
func printJSON(o any) {
	if args.Output == "json" || args.Output == "ndjson" {
		j, _ := json.Marshal(o)
		fmt.Println(string(j))
		if args.Output == "ndjson" {
			if f, ok := os.Stdout.Stat(); ok == nil && f != nil {
				// Stdout may be a pipe or file; Sync is a best-effort flush.
				_ = os.Stdout.Sync()
			}
		}
	}
}

// buildTransport assembles the shared http.Transport based on the CLI flags.
// Centralised so Run() stays readable and tests can exercise it in isolation.
func buildTransport(p *arg.Parser) *http.Transport {
	tlsCfg := &tls.Config{
		InsecureSkipVerify: args.Insecure,
		Renegotiation:      tls.RenegotiateOnceAsClient,
	}
	// Merge in an extra CA bundle (corporate / internal PKI).
	if args.CA != "" {
		data, err := os.ReadFile(args.CA)
		if err != nil {
			p.Fail(fmt.Sprintf("unable to read --ca file %q: %s", args.CA, err))
		}
		pool, _ := x509.SystemCertPool()
		if pool == nil {
			pool = x509.NewCertPool()
		}
		if !pool.AppendCertsFromPEM(data) {
			p.Fail(fmt.Sprintf("no PEM certificates found in --ca file %q", args.CA))
		}
		tlsCfg.RootCAs = pool
	}
	proxyFn := http.ProxyFromEnvironment
	if args.Proxy != "" {
		u, err := nurl.Parse(args.Proxy)
		if err != nil {
			p.Fail(fmt.Sprintf("unable to parse --proxy %q: %s", args.Proxy, err))
		}
		switch u.Scheme {
		case "http", "https":
			proxyFn = http.ProxyURL(u)
		case "":
			u.Scheme = "http"
			proxyFn = http.ProxyURL(u)
		default:
			p.Fail(fmt.Sprintf("unsupported proxy scheme %q (use http:// or https://)", u.Scheme))
		}
	}
	// Pool tuning -- Go defaults to MaxIdleConnsPerHost=2 which thrashes TLS
	// handshakes when concurrency is high.
	c := args.Concurrency
	if c < 1 {
		c = 1
	}
	return &http.Transport{
		TLSClientConfig:       tlsCfg,
		Proxy:                 proxyFn,
		MaxIdleConns:          c * 4,
		MaxIdleConnsPerHost:   c * 2,
		MaxConnsPerHost:       0,
		IdleConnTimeout:       90 * time.Second,
		TLSHandshakeTimeout:   10 * time.Second,
		ExpectContinueTimeout: 1 * time.Second,
		DisableCompression:    false,
		ForceAttemptHTTP2:     true,
	}
}

// hashHit implements the `hash` autocomplete mode.  It builds a bucket of
// SHA-256 fingerprints + content-length bounds from a handful of known-miss
// responses for the given extension, then checks whether the response we just
// got falls outside that bucket.  Cheap, O(n), tolerant of randomised CSRF
// tokens that cause Levenshtein to flap.
func hashHit(c wordlistRecord, br baseRequest, hc *http.Client, st *httpStats, res *http.Response) bool {
	hashMutex.Lock()
	if hashCache == nil {
		hashCache = make(map[string]map[int]*hashBucket)
	}
	per, ok := hashCache[c.extension]
	if !ok {
		per = make(map[int]*hashBucket)
		hashCache[c.extension] = per
	}
	hashMutex.Unlock()

	// Populate the bucket lazily: sample a handful of random-miss URLs for this
	// extension and keep their body SHAs + length band per-status-code.
	samples := 4
	if args.Stabilise {
		samples = 12
	}
	hashMutex.Lock()
	// Is any bucket populated?  If the extension has never been sampled, do so.
	unsampled := true
	for _, b := range per {
		if b.populated {
			unsampled = false
			break
		}
	}
	hashMutex.Unlock()
	if unsampled {
		for i := 0; i < samples; i++ {
			p := randPath(rand.Intn(4)+8, 0, alphanum) + c.extension
			r, err := fetch(hc, st, "GET", br.url+p)
			if err != nil {
				continue
			}
			body, _ := io.ReadAll(io.LimitReader(r.Body, 4096))
			sum := sha256.Sum256(body)
			key := hex.EncodeToString(sum[:])
			hashMutex.Lock()
			b, ok := per[r.StatusCode]
			if !ok {
				b = &hashBucket{sums: make(map[string]struct{}), minLen: len(body), maxLen: len(body)}
				per[r.StatusCode] = b
			}
			b.sums[key] = struct{}{}
			if len(body) < b.minLen {
				b.minLen = len(body)
			}
			if len(body) > b.maxLen {
				b.maxLen = len(body)
			}
			b.populated = true
			hashMutex.Unlock()
		}
	}

	// Now compare the response we got against the bucket for its status code.
	body, _ := io.ReadAll(io.LimitReader(res.Body, 4096))
	sum := sha256.Sum256(body)
	key := hex.EncodeToString(sum[:])
	hashMutex.Lock()
	defer hashMutex.Unlock()
	b, ok := per[res.StatusCode]
	if !ok || !b.populated {
		// We have no miss fingerprint for this status code -> treat as a hit.
		return true
	}
	if _, known := b.sums[key]; known {
		return false
	}
	// SHA is new; also require the length to fall outside the miss band by at
	// least a tolerance of 16 bytes to cut down on false positives from date
	// stamps / CSRF tokens.
	const tol = 16
	if len(body) < b.minLen-tol || len(body) > b.maxLen+tol {
		return true
	}
	return true // new SHA and similar length -> still a hit; length already noisy
}

// detectFingerprint parses a bag of response headers and returns what we think
// we're talking to.  Used to reorder probe attempts.
func detectFingerprint(h http.Header) iisFingerprint {
	fp := iisFingerprint{}
	if v := h.Get("Server"); v != "" {
		fp.server = v
		ls := strings.ToLower(v)
		if strings.Contains(ls, "microsoft-iis/") {
			fp.isIIS = true
			// Parse "Microsoft-IIS/10.0" -> majorVersion = 10
			idx := strings.Index(ls, "microsoft-iis/")
			rest := ls[idx+len("microsoft-iis/"):]
			if dot := strings.IndexAny(rest, ". \t"); dot > 0 {
				rest = rest[:dot]
			}
			if n, err := strconv.Atoi(rest); err == nil {
				fp.majorVersion = n
			}
		}
		if strings.Contains(ls, "kestrel") {
			fp.kestrelFront = true
		}
	}
	if v := h.Get("X-Aspnet-Version"); v != "" {
		fp.aspNet = true
	}
	if v := h.Get("X-Powered-By"); v != "" {
		lv := strings.ToLower(v)
		if strings.Contains(lv, "asp.net") {
			fp.aspNet = true
		}
		if strings.Contains(lv, "php") {
			fp.poweredByPHP = true
		}
	}
	if v := h.Get("X-AspNetMvc-Version"); v != "" {
		fp.aspNet = true
	}
	// Common WAF banners (non-exhaustive, advisory only).
	for _, k := range []string{"Cf-Ray", "X-Sucuri-Id", "X-Iinfo", "X-Cdn", "X-Amz-Cf-Id", "X-Akamai-Transformed"} {
		if h.Get(k) != "" {
			fp.hasWAFMarkers = true
			break
		}
	}
	return fp
}

// prioritiseProbeOrder returns reordered copies of (suffixes, methods) placing
// the combinations most likely to work first.  The rest of the slices keep
// their relative order so `--patience` can still cover everything.
func prioritiseProbeOrder(fp iisFingerprint, suffixes []string, methods []string) ([]string, []string) {
	front := func(slice []string, preferred ...string) []string {
		out := make([]string, 0, len(slice))
		seen := make(map[string]bool)
		for _, p := range preferred {
			for _, s := range slice {
				if s == p && !seen[s] {
					out = append(out, s)
					seen[s] = true
				}
			}
		}
		for _, s := range slice {
			if !seen[s] {
				out = append(out, s)
				seen[s] = true
			}
		}
		return out
	}
	switch {
	case fp.majorVersion >= 10 || fp.kestrelFront:
		// Modern IIS / ASP.NET Core: DEBUG + GET routinely filtered, the
		// handler-specific suffixes carry best.
		methods = front(methods, "OPTIONS", "HEAD", "GET", "POST")
		suffixes = front(suffixes, "/.aspx", "/.asmx", "/.ashx", "/.svc", "/a.aspx", "/", "")
	case fp.majorVersion == 7 || fp.majorVersion == 8:
		methods = front(methods, "DEBUG", "OPTIONS", "GET", "HEAD")
		suffixes = front(suffixes, "/.aspx", "?aspxerrorpath=/", "/", "")
	case fp.majorVersion == 6:
		methods = front(methods, "OPTIONS", "GET", "HEAD")
		suffixes = front(suffixes, "/", "", "/.aspx")
	}
	return suffixes, methods
}

// probeReservedNames hits CON, PRN, AUX, NUL and the COM*/LPT* device names.
// The Windows I/O manager refuses to open these files, so the ASP.NET pipeline
// typically serves an unhandled-exception page that leaks the physical path.
func probeReservedNames(url string, ac *attackConfig, hc *http.Client, st *httpStats) {
	for _, rn := range reservedNames {
		target := url + rn
		if ac.suffix != "" {
			target += ac.suffix
		}
		res, err := fetchFromAttack(hc, st, ac, target)
		if err != nil || res == nil {
			continue
		}
		if res.StatusCode == 500 || res.StatusCode == 200 {
			log.WithFields(log.Fields{"url": target, "status": res.StatusCode}).Info("Reserved-name probe produced suspicious response")
			printHuman(color.New(color.FgYellow, color.Bold).Sprint("[reserved]"), rn, color.HiBlackString(fmt.Sprintf("status=%d", res.StatusCode)))
			if args.Output == "json" || args.Output == "ndjson" {
				printJSON(map[string]any{"type": "reserved", "url": target, "status": res.StatusCode})
			}
		}
	}
}

// Scan starts enumeration of the given URLs.
// A shared "visited" map is passed so that no URL is processed more than once.
func Scan(urls []string, hc *http.Client, st *httpStats, wc wordlistConfig, mk markers, visited map[string]struct{}) {
	// Main loop while there are URLs in the queue
	for len(urls) > 0 {
		var url string
		url, urls = urls[0], urls[1:]
		url = strings.TrimSuffix(url, "/") + "/"

		// Skip if URL has already been visited
		if _, ok := visited[url]; ok {
			continue
		}
		visited[url] = struct{}{}

		// Default to HTTPS if no protocol is provided
		if !strings.Contains(url, "://") {
			url = "https://" + url
		}

		// Pre-flight: validate URL and check accessibility
		if _, err := nurl.Parse(url); err != nil {
			log.WithFields(log.Fields{"url": url, "error": err}).Error("Unable to parse URL")
			continue
		}
		res, err := fetch(hc, st, "GET", url+".aspx")
		if err != nil {
			log.WithFields(log.Fields{"error": err}).Error("Unable to access server")
			continue
		}

		printHuman("\n════════════════════════════════════════════════════════════════════════════════")
		printHuman(color.New(color.FgWhite, color.Bold).Sprint("URL")+":", url)
		srv := "<unknown>"
		if len(res.Header["Server"]) > 0 {
			srv = strings.Join(res.Header["Server"], ", ")
		}
		if v, ok := res.Header["X-Aspnet-Version"]; ok {
			srv += " (ASP.NET v" + v[0] + ")"
		}
		if args.Output == "human" && srv != "<unknown>" && !strings.Contains(srv, "IIS") && !strings.Contains(srv, "ASP") {
			srv += " " + color.HiRedString("[!]")
		}
		printHuman(color.New(color.FgWhite, color.Bold).Sprint("Running")+":", srv)

		// Derive an IIS fingerprint from the headers to steer probe ordering.
		fp := detectFingerprint(res.Header)
		globalFingerprint.Store(fp)
		if fp.hasWAFMarkers {
			log.Info("WAF-style markers detected in banner; verb-override fallback recommended")
		}

		// Set up autocomplete mode
		if args.Autocomplete == "auto" {
			if res, err := fetch(hc, st, "_", url); err == nil && res.StatusCode == 405 {
				args.Autocomplete = "method"
				log.Info("Using method-based file existence checks")
			} else {
				args.Autocomplete = "status"
				log.Info("Using status-based file existence checks")
			}
		}

		// First stage: check if the server is vulnerable
		ac := attackConfig{wordlist: wc}
		var pc, mc int
		if args.Patience == 1 {
			pc = len(pathSuffixes)
			mc = len(httpMethods)
		} else {
			pc = 4
			mc = 9
		}
		if pc > len(pathSuffixes) {
			pc = len(pathSuffixes)
		}
		if mc > len(httpMethods) {
			mc = len(httpMethods)
		}
		// Pull the fingerprint-prioritised ordering so high-probability
		// verb/suffix combinations are tried first.
		probeSuffixes, probeMethods := prioritiseProbeOrder(fp, pathSuffixes[:pc], httpMethods[:mc])

		// Two passes: first direct verbs, second (if --verb-override) via the
		// X-HTTP-Method-Override header chain.  The override pass keeps the
		// wire verb stable at POST and smuggles the real verb in headers.
		overridePasses := []string{""}
		if args.VerbOverride {
			overridePasses = append(overridePasses, "POST")
		}
	outerEscape:
		for _, override := range overridePasses {
			for _, suffix := range probeSuffixes {
			methodEscape:
				for _, method := range probeMethods {
					if override != "" && method == override {
						continue // overriding POST as POST is pointless
					}
					var statusNeg int
					validMarkers := struct{ status bool }{true}
					for i := 0; i < 4; i++ {
						res, err := fetchWithOverride(hc, st, method, override, fmt.Sprintf("%s*%d*%s", url, rand.Intn(5)+5, suffix))
						if err != nil {
							log.Debug("Method " + method + " failed, skipping")
							continue methodEscape
						}
						status := res.StatusCode
						if statusNeg != 0 && status != statusNeg {
							log.WithFields(log.Fields{"status": status, "statusNeg": statusNeg}).Debug("Method " + method + " unstable, skipping")
							continue methodEscape
						}
						statusNeg = status
					}
					if validMarkers.status {
						maxTilde := args.MaxTilde
						if args.DeepTilde {
							maxTilde = 9
						}
						if maxTilde < 1 {
							maxTilde = 4
						}
						if maxTilde > 9 {
							maxTilde = 9
						}
						for i := 1; i <= maxTilde; i++ {
							res, err := fetchWithOverride(hc, st, method, override, fmt.Sprintf("%s*~%d*%s", url, i, suffix))
							if err == nil {
								statusPos := res.StatusCode
								if validMarkers.status && statusPos != statusNeg {
									res, _ := fetchWithOverride(hc, st, method, override, fmt.Sprintf("%s*~0*%s", url, suffix))
									if statusPos == res.StatusCode {
										log.WithFields(log.Fields{"statusPos": statusPos, "statusNeg": statusNeg}).Debug("Negative response differed, could be rate limiting or server instability")
									} else {
										ac.tildes = append(ac.tildes, fmt.Sprintf("~%d", i))
										mk.statusPos = statusPos
										mk.statusNeg = statusNeg
									}
								}
							}
						}
						if len(ac.tildes) > 0 {
							ac.method = method
							ac.suffix = suffix
							ac.override = override
							break outerEscape
						}
					}
				}
			}
			if args.VerbOverride && override == "" && len(ac.tildes) == 0 {
				log.Info("Direct verb probe failed; retrying with X-HTTP-Method-Override header chain")
			}
		}

		printJSON(statusOutput{Type: "status", Url: url, Server: srv, Vulnerable: len(ac.tildes) > 0})
		if len(ac.tildes) == 0 {
			printHuman(color.New(color.FgWhite, color.Bold).Sprint("Vulnerable:"), color.HiBlueString("No"), "(or no 8.3 files exist)")
			printHuman("════════════════════════════════════════════════════════════════════════════════")
			continue
		}

		printHuman(color.New(color.FgWhite, color.Bold).Sprint("Vulnerable:"), color.HiRedString("Yes!"))
		printHuman("════════════════════════════════════════════════════════════════════════════════")
		log.WithFields(log.Fields{"method": ac.method, "suffix": ac.suffix, "statusPos": mk.statusPos, "statusNeg": mk.statusNeg}).Info("Found working options")
		log.WithFields(log.Fields{"tildes": ac.tildes}).Info("Found tilde files")
		if args.IsVuln {
			continue
		}

		// Second stage: determine which characters are in use
		ac.fileChars, ac.extChars = make(map[string]string), make(map[string]string)
		for i := 0; i < 2; i++ {
			for _, char := range args.Characters {
				for _, tilde := range ac.tildes {
					var cu string
					var cm map[string]string
					if i == 0 {
						cm = ac.fileChars
						cu = url + "*" + pathEscape(string(char)) + "*" + tilde + "*" + ac.suffix
					} else {
						cm = ac.extChars
						cu = url + "*" + tilde + "*" + pathEscape(string(char)) + "*" + ac.suffix
					}
					res, err := fetchFromAttack(hc, st, &ac, cu)
					if err == nil && res.StatusCode != mk.statusNeg {
						cm[tilde] = cm[tilde] + string(char)
					}
				}
			}
		}
		log.WithFields(log.Fields{"fileChars": ac.fileChars, "extChars": ac.extChars}).Info("Built character set")

		// Optional reserved-name probe (runs once we've confirmed vulnerability).
		if args.Reserved {
			probeReservedNames(url, &ac, hc, st)
		}

		// Third stage: full enumeration
		ac.foundFiles = make(map[string]struct{})
		ac.foundDirectories = make(map[string]struct{})
		sem := make(chan struct{}, args.Concurrency)
		wg := new(sync.WaitGroup)
		for _, tilde := range ac.tildes {
			enumerate(sem, wg, hc, st, &ac, mk, baseRequest{url: url, file: "", tilde: tilde, ext: ""})
		}
		wg.Wait()

		// Record the URL as fully scanned, for resume support.
		if globalCheckpoint != nil {
			globalCheckpoint.write(checkpointRecord{Type: "visit", URL: url})
		}

		// Prepend discovered directories for further processing
		for dir := range ac.foundDirectories {
			urls = append([]string{url + dir + "/"}, urls...)
		}

		// Regressive (backwards) scan: if the flag is set, compute the parent URL and add it if not already visited.
		if args.BackwardsRecurse {
			parsed, err := nurl.Parse(url)
			if err != nil {
				log.WithFields(log.Fields{"url": url, "error": err}).Error("Failed to parse URL for backwards scanning")
			} else {
				currentPath := strings.TrimSuffix(parsed.Path, "/")
				if currentPath == "" {
					currentPath = "/"
				}
				parentPath := path.Dir(currentPath)
				if parentPath == "." || parentPath == "" {
					parentPath = "/"
				}
				if parentPath != currentPath {
					parsed.Path = parentPath
					newURL := parsed.Scheme + "://" + parsed.Host + parsed.Path
					if !strings.HasSuffix(newURL, "/") {
						newURL += "/"
					}
					// Only add the parent URL if it hasn't been visited
					if _, exists := visited[newURL]; !exists {
						urls = append(urls, newURL)
						printHuman("Added regressive scan URL: ", newURL)
					}
				}
			}
		}

		printHuman("════════════════════════════════════════════════════════════════════════════════")
	}
	printHuman()
	printHuman(fmt.Sprintf("%s Requests: %d; Retries: %d; Sent %d bytes; Received %d bytes",
		color.New(color.FgWhite, color.Bold).Sprint("Finished!"), st.requests, st.retries, st.bytesTx, st.bytesRx))
	printJSON(statsOutput{Type: "statistics", Requests: st.requests, Retries: st.retries, SentBytes: st.bytesTx, ReceivedBytes: st.bytesRx})
}

// Run kicks off scans from the command line
func Run() {
	rand.Seed(time.Now().UTC().UnixNano())
	p := arg.MustParse(&args)
	args.Autocomplete = strings.ToLower(args.Autocomplete)
	switch args.Autocomplete {
	case "auto", "method", "status", "distance", "hash", "none":
	default:
		p.Fail("autocomplete must be one of: auto, status, method, distance, hash, none")
	}
	args.Output = strings.ToLower(args.Output)
	switch args.Output {
	case "human", "json", "ndjson":
	default:
		p.Fail("output must be one of: human, json, ndjson")
	}
	if args.MaxTilde < 1 || args.MaxTilde > 9 {
		p.Fail("--max-tilde must be between 1 and 9")
	}
	if args.DeepTilde && args.MaxTilde < 9 {
		args.MaxTilde = 9
	}
	if args.RPS < 0 {
		p.Fail("--rps must be >= 0")
	}

	printHuman(getBanner())

	// Warn if any filename characters are invalid
	for _, c := range []string{"<", ">", ":", "\"", "/", "\\", "|", "?", "*"} {
		if strings.Contains(args.Characters, c) {
			log.WithFields(log.Fields{"character": c}).Warn("Invalid filename character; weird things may happen")
		}
	}

	log.SetFormatter(&log.TextFormatter{
		DisableLevelTruncation: true,
		DisableTimestamp:       true,
	})
	if args.Verbosity > 1 {
		log.SetLevel(log.TraceLevel)
	} else if args.Verbosity > 0 {
		log.SetLevel(log.DebugLevel)
	} else {
		log.SetLevel(log.WarnLevel)
	}

	hc := &http.Client{
		Timeout:       time.Duration(args.Timeout) * time.Second,
		Transport:     buildTransport(p),
		CheckRedirect: func(req *http.Request, via []*http.Request) error { return http.ErrUseLastResponse },
	}

	mk := markers{}
	st := &httpStats{}
	wc := wordlistConfig{}
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	checksumRegex = regexp.MustCompile(".{1,2}[0-9A-F]{4}")

	var s *bufio.Scanner
	if args.Wordlist != "" {
		log.WithFields(log.Fields{"file": args.Wordlist}).Info("Using custom wordlist")
		fh, err := os.Open(args.Wordlist)
		if err != nil {
			log.WithFields(log.Fields{"err": err}).Fatal("Unable to open wordlist")
		}
		s = bufio.NewScanner(fh)
	} else {
		log.Info("Using built-in wordlist")
		fh, _ := defaultWordlist.Open("resources/wordlist.txt")
		s = bufio.NewScanner(fh)
	}

	n := 0
	for s.Scan() {
		line := s.Text()
		if n == 0 && line == rainbowMagic {
			wc.isRainbow = true
			log.Info("Rainbow table provided, enabling auto dechecksumming")
			continue
		}
		if l := len(line); l == 0 || line[0] == '#' {
			continue
		}
		if wc.isRainbow {
			if strings.Count(line, "\t") != 4 {
				log.WithFields(log.Fields{"line": line}).Fatal("Wordlist entry invalid (incorrect tab count)")
			}
			c := strings.Split(line, "\t")
			f, e, f83, e83 := c[3], c[4], c[1], c[2]
			if len(e) > 0 {
				e = "." + e
			}
			wc.wordlist = append(wc.wordlist, wordlistRecord{c[0], f, e, f83, e83})
		} else {
			var r wordlistRecord
			if p := strings.LastIndex(line, "."); p > 0 && line[0] != '.' {
				f, e := line[:p], line[p:]
				_, f83, e83 := shortutil.Gen8dot3(f, e)
				r = wordlistRecord{"", f, e, f83, e83}
			} else {
				_, f83, _ := shortutil.Gen8dot3(line, "")
				r = wordlistRecord{"", line, "", f83, ""}
			}
			wc.wordlist = append(wc.wordlist, r)
		}
		n++
	}

	if args.List != "" {
		f, err := os.Open(args.List)
		if err != nil {
			log.WithFields(log.Fields{"err": err}).Fatal("Unable to open URL list file")
		}
		scanner := bufio.NewScanner(f)
		for scanner.Scan() {
			args.Urls = append(args.Urls, scanner.Text())
		}
		if err := scanner.Err(); err != nil {
			log.WithFields(log.Fields{"err": err}).Fatal("Error reading URL list file")
		}
	}

	// Initialise the shared rate limiter (nil if both --rps == 0 and
	// --adaptive disabled, in which case fetch() skips the wait entirely).
	if args.RPS > 0 || args.Adaptive {
		globalLimiter = newRateLimiter(args.RPS, args.Adaptive)
		if args.RPS > 0 {
			log.WithFields(log.Fields{"rps": args.RPS, "adaptive": args.Adaptive}).Info("Rate limiter enabled")
		}
	}

	// Initialise checkpoint, replaying any prior state.
	var seededHits map[string]map[string]bool
	seededVisits := map[string]struct{}{}
	if args.Checkpoint != "" {
		cp, state, visits, err := newCheckpointWriter(args.Checkpoint)
		if err != nil {
			log.WithFields(log.Fields{"err": err, "path": args.Checkpoint}).Fatal("Unable to open checkpoint file")
		}
		globalCheckpoint = cp
		seededHits = state
		seededVisits = visits
		defer cp.close()
		if len(visits) > 0 || len(state) > 0 {
			log.WithFields(log.Fields{"visits": len(visits), "hosts_with_hits": len(state)}).Info("Checkpoint replayed")
		}
	}
	_ = seededHits // reserved for future cross-host seeding; per-host seeding currently handled via visited map

	if args.Index && len(args.Urls) > 0 {
		testIndexAllocations(args.Urls, hc, st, wc, mk)
		return
	}

	// Create a global visited map so that paths are not re-scanned.  Seed
	// from the checkpoint so a resumed run skips URLs already completed.
	visited := make(map[string]struct{})
	for u := range seededVisits {
		visited[u] = struct{}{}
	}
	Scan(args.Urls, hc, st, wc, mk, visited)
}