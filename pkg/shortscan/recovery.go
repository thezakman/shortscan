package shortscan

import (
	"fmt"
	"io"
	"math/rand"
	"net/http"
	nurl "net/url"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"unicode/utf16"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
	"github.com/thezakman/shortscan/pkg/levenshtein"
	"github.com/thezakman/shortscan/pkg/maths"
	"github.com/thezakman/shortscan/pkg/shortutil"
)

type distances struct {
	distance float32
	body     string
	samples  int
}

type filenameCandidate struct {
	record    wordlistRecord
	matchType string
	source    string
	// checksum and families are populated only for checksum-mask and
	// collision-ancestry candidates; they carry provenance into the output.
	checksum string
	families []string
}

// frameworkManifestNames are conventional root files whose names are part of
// the ASP.NET/NuGet ecosystem rather than site-specific guesses. They are still
// only candidates: requestFiltering prevents direct HTTP confirmation for these
// extensions, so the fallback labels them inferred and never counts them as a
// resolved long name. Keeping them explicit fixes ambiguous corpus ordering such
// as PACKAGE.CONFIG winning over the canonical NuGet packages.config, and covers
// AjaxControlToolkit.config even when the generic wordlist lacks its .config form.
var frameworkManifestNames = [...]string{
	"AjaxControlToolkit.config",
	"AppSettings.config",
	"packages.config",
	"web.config",
	"Global.asax",
}

func frameworkManifestCandidates(br baseRequest) []filenameCandidate {
	shortExtension := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
	var out []filenameCandidate
	for _, name := range frameworkManifestNames {
		dot := strings.LastIndex(name, ".")
		if dot <= 0 {
			continue
		}
		stem, extension := name[:dot], name[dot:]
		_, filename83, extension83 := shortutil.Gen8dot3(stem, extension)
		if !strings.EqualFold(filename83, br.file) || !strings.EqualFold(extension83, shortExtension) {
			continue
		}
		out = append(out, filenameCandidate{
			record: wordlistRecord{
				filename: stem, extension: extension,
				filename83: filename83, extension83: extension83,
			},
			matchType: "framework-manifest",
			source:    "ASP.NET/NuGet conventional project manifest",
		})
	}
	return out
}

// Well-known extensions are paired with a matching filename stem when the
// enumerated 8.3 extension is only a prefix (for example, ASP can be ASPX).
// The generated candidate is still verified over HTTP before it is reported
// as a recovered filename.
var wellKnownExtensions = [...]string{
	// ASP.NET handlers / source
	".asp", ".aspx", ".asax", ".ascx", ".asmx", ".ashx", ".axd", ".rem",
	".cs", ".cshtml", ".vb", ".vbhtml", ".razor", ".svc", ".compiled",
	".master", ".sitemap", ".browser", ".resx", ".resources", ".dll", ".pdb",
	// project / build / provenance
	".csproj", ".vbproj", ".sln", ".nupkg", ".snk", ".licx", ".edmx", ".dbml",
	// other web stacks that co-host on Windows/IIS
	".php", ".phtml", ".php5", ".php7", ".jsp", ".jspx", ".cfm", ".do", ".action",
	// config / secrets
	".config", ".settings", ".cscfg", ".publishsettings", ".pubxml", ".disco",
	".yaml", ".yml", ".toml", ".ini", ".env", ".properties",
	// data / db
	".json", ".xml", ".wsdl", ".xsd", ".soap", ".sql", ".sqlite", ".db",
	".mdf", ".ldf", ".csv", ".xls", ".xlsx", ".doc", ".docx",
	// markup / frontend source
	".html", ".htm", ".xhtml", ".js", ".mjs", ".cjs", ".ts", ".tsx", ".jsx",
	".vue", ".css", ".scss", ".sass", ".less", ".map", ".webmanifest",
	// assets
	".wasm", ".svg", ".woff", ".woff2", ".ttf", ".otf", ".txt", ".log", ".md",
	// keys / certs
	".cer", ".crt", ".der", ".pfx", ".p12", ".jks", ".keystore", ".key", ".pem",
	// archives / backups / temp
	".br", ".gz", ".zip", ".7z", ".rar", ".bak", ".backup", ".old", ".orig",
	".save", ".tmp", ".swp", ".inc", ".tpl", ".lock",
}

// inspectDisclosure inspects a response body for source-code/binary disclosure signatures.
// Returns (disclosed, type) where type is e.g. "MZ binary", "ZIP/PK archive", "ASP.NET source", etc.
func inspectDisclosure(body []byte) (bool, string) {
	if len(body) < 2 {
		return false, ""
	}
	// Magic bytes
	if body[0] == 0x4D && body[1] == 0x5A {
		return true, "MZ binary (.dll/.exe)"
	}
	if len(body) >= 4 && body[0] == 0x50 && body[1] == 0x4B && body[2] == 0x03 && body[3] == 0x04 {
		return true, "ZIP/PK archive"
	}
	// IIS's built-in webdav_simple_prop provider writes properties.dav as UTF-16LE.
	// A non-IIS tier on the same NTFS root can serve this Hidden+System file through
	// its 8.3 alias even when the canonical name is denied. Recognise the store so a
	// recovered PROPER~N.DAV is reported as data disclosure, not generic binary noise.
	if len(body) >= 4 && body[0] == 0xff && body[1] == 0xfe && len(body)%2 == 0 {
		words := make([]uint16, 0, (len(body)-2)/2)
		for i := 2; i+1 < len(body); i += 2 {
			words = append(words, uint16(body[i])|uint16(body[i+1])<<8)
		}
		u := strings.ToLower(string(utf16.Decode(words)))
		if strings.HasPrefix(strings.TrimSpace(u), "[/") && strings.Contains(u, "]") && strings.Contains(u, "=1") {
			return true, "IIS WebDAV property store (properties.dav)"
		}
	}
	s := strings.ToLower(string(body))
	switch {
	case strings.Contains(s, "<%@"):
		return true, "ASP/ASP.NET source"
	case strings.Contains(s, "using system;") || strings.Contains(s, "namespace "):
		return true, "C# source"
	case strings.Contains(s, "<configuration>") && strings.Contains(s, "connectionstring"):
		return true, "web.config / connection string"
	case strings.Contains(s, "-----begin "):
		return true, "PEM key/certificate"
	case strings.Contains(s, "appsettings") && strings.Contains(s, "\"connectionstrings\""):
		return true, "appsettings.json"
	}
	return false, ""
}

// Caches and regexes
var statusCache map[string]map[int]struct{}
var distanceCache map[string]map[int]distances
var checksumRegex *regexp.Regexp
var cacheMutex sync.RWMutex

// vulnerableCount tracks how many URLs were marked vulnerable by Scan().
// Used by testIndexAllocations to fall back to ADS variants only when needed.
var vulnerableCount int

type recoveryMatch struct {
	path            string
	baseURL         string
	matchType       string
	status          int
	collisionGroup  string
	ordinalVerified bool
	oracle          string
	method          string
	suffix          string
	checksum        string
	derivedFrom     string
	families        []string
}

var (
	bruteStatuses         map[int]struct{}
	candidateOutputWriter io.Writer
	candidateOutputMutex  sync.Mutex
	candidateOutputSeen   map[string]struct{}
)

func parseStatusCodes(spec string) (map[int]struct{}, error) {
	statuses := make(map[int]struct{})
	for _, item := range strings.Split(spec, ",") {
		item = strings.TrimSpace(item)
		if item == "" {
			continue
		}
		if strings.Contains(item, "-") {
			bounds := strings.SplitN(item, "-", 2)
			start, startErr := strconv.Atoi(strings.TrimSpace(bounds[0]))
			end, endErr := strconv.Atoi(strings.TrimSpace(bounds[1]))
			if startErr != nil || endErr != nil || start > end || start < 100 || end > 599 {
				return nil, fmt.Errorf("invalid status range %q", item)
			}
			for status := start; status <= end; status++ {
				statuses[status] = struct{}{}
			}
			continue
		}
		status, err := strconv.Atoi(item)
		if err != nil || status < 100 || status > 599 {
			return nil, fmt.Errorf("invalid HTTP status %q", item)
		}
		statuses[status] = struct{}{}
	}
	if len(statuses) == 0 {
		return nil, fmt.Errorf("at least one HTTP status is required")
	}
	return statuses, nil
}

func sameFilePath(left, right string) bool {
	if left == "" || right == "" {
		return false
	}
	leftInfo, leftStatErr := os.Stat(left)
	rightInfo, rightStatErr := os.Stat(right)
	if leftStatErr == nil && rightStatErr == nil && os.SameFile(leftInfo, rightInfo) {
		return true
	}
	leftPath, leftErr := filepath.Abs(left)
	rightPath, rightErr := filepath.Abs(right)
	if leftErr != nil || rightErr != nil {
		return filepath.Clean(left) == filepath.Clean(right)
	}
	// Output files may not exist yet. Resolve their existing parent directories
	// so two spellings through a directory symlink cannot open the same output
	// twice (or interleave the result and candidate streams).
	if parent, err := filepath.EvalSymlinks(filepath.Dir(leftPath)); err == nil {
		leftPath = filepath.Join(parent, filepath.Base(leftPath))
	}
	if parent, err := filepath.EvalSymlinks(filepath.Dir(rightPath)); err == nil {
		rightPath = filepath.Join(parent, filepath.Base(rightPath))
	}
	return filepath.Clean(leftPath) == filepath.Clean(rightPath)
}

func shortNameSelected(br baseRequest) bool {
	if len(args.ProbeShorts) == 0 {
		return true
	}
	shortName := br.file + br.tilde + br.ext
	shortStem := br.file + br.tilde
	for _, selected := range args.ProbeShorts {
		selected = strings.TrimSpace(selected)
		if strings.EqualFold(selected, shortName) || strings.EqualFold(selected, shortStem) {
			return true
		}
	}
	return false
}

func recoveryBaseURL(br baseRequest) string {
	if strings.EqualFold(br.ext, ".dll") {
		return replaceBinALLOCATION(br.url)
	}
	return br.url
}

// shortCollisionGroup describes what long-name recovery can actually prove.
// A long filename that matches PAGEDL~1.DLL also matches the same six-character
// candidate set as PAGEDL~2.DLL. The ordinal is assigned from NTFS creation
// state and cannot be reconstructed from a successful long-path request alone.
func shortCollisionGroup(br baseRequest) string {
	return br.file + "~*" + br.ext
}

func candidateVerifiesOrdinal(br baseRequest, candidatePath string) bool {
	return strings.EqualFold(candidatePath, br.file+br.tilde+br.ext)
}

func boolPointer(value bool) *bool {
	return &value
}

func emitCandidateURL(candidateURL string) {
	if candidateOutputWriter == nil {
		return
	}
	candidateOutputMutex.Lock()
	defer candidateOutputMutex.Unlock()
	if candidateOutputSeen == nil {
		candidateOutputSeen = make(map[string]struct{})
	}
	if _, exists := candidateOutputSeen[candidateURL]; exists {
		return
	}
	candidateOutputSeen[candidateURL] = struct{}{}
	fmt.Fprintln(candidateOutputWriter, candidateURL)
}

// foundFileKey normalises a recovered-file path to a case-insensitive dedup key.
// IIS/NTFS resolve /Dir/File and /dir/FILE to the same physical file, so a
// recovery path that differs only in case — a wordlist's lowercase name vs a
// crawl's on-disk casing (test.html vs TEST.html) — must dedup to one entry;
// otherwise sibling/reference recovery re-reports a name already resolved.
func foundFileKey(path string) string { return strings.ToLower(path) }

// markResolvedFile records a newly-confirmed long name. It only touches
// ac.foundFiles/ac.foundDirectories (fast, synchronous map writes) — every
// caller holds ac.autocompleteMutex around this call and MUST follow it with
// enrichResolvedFile (below) after releasing that lock. The two used to be
// one function that made its network calls while still holding the lock;
// see enrichResolvedFile's doc comment for why that was a real bottleneck.
func markResolvedFile(ac *attackConfig, br baseRequest, baseURL, candidatePath string) {
	ac.foundFiles[foundFileKey(candidatePath)] = struct{}{}
	rememberReferenceSeed(ac, baseURL, candidatePath)

	// An extensionless 8.3 match does not tell us whether the recovered path is
	// a file or a directory. Queue it for Scan's normal vulnerability pre-flight
	// instead of relying exclusively on a trailing-slash redirect. Reverse
	// proxies, rewrites, protected directories, and servers with HEAD disabled
	// commonly suppress that redirect; the nested short-name oracle is the more
	// reliable (and self-limiting) confirmation step.
	if args.Recurse && br.ext == "" {
		ac.foundDirectories[candidatePath] = struct{}{}
		log.WithFields(log.Fields{"url": baseURL + candidatePath}).Info("Queued recovered extensionless path for recursive validation")
	}
}

// enrichResolvedFile runs the network-bound follow-ups for a newly confirmed
// long name: up to 10 sequential --mutate-ext probes (probeMutations),
// --inspect-source's body fetch, and (--recurse, extension present) a HEAD
// to check for a directory redirect — as many as ~12 sequential HTTP
// round-trips. markResolvedFile used to make these same calls WHILE the
// caller's ac.autocompleteMutex was still held; every one of markResolvedFile's
// 7 call sites (recovery.go x3, collision.go, references.go, sibling.go,
// stembrute.go) runs inside a concurrent worker, so that serialized EVERY
// worker on the same host behind whichever one was enriching a match — on a
// heavily-vulnerable target under --full (many matches, each paying up to
// ~12 request timeouts back to back) this could make one host's scan take
// enormously, unboundedly longer than --maxtime accounts for (none of these
// callers check it), presenting as a stalled/hung scan. Call this AFTER
// releasing the lock; it only re-acquires it for the final
// ac.foundDirectories write, which needs the same protection foundFiles does.
func enrichResolvedFile(hc *http.Client, st *httpStats, ac *attackConfig, br baseRequest, baseURL, candidatePath string) {
	resolvedRequest := br
	resolvedRequest.url = baseURL
	probeMutations(hc, st, ac, baseURL, candidatePath)
	inspectResolvedFile(hc, st, ac, resolvedRequest, candidatePath)
	if args.Auto || args.Full {
		// Quiet PathInfo file-read candidate check on resolved handler names
		// (.aspx/.ashx/.asmx/.svc); prints only a medium/high candidate.
		pathInfoProbeAuto(hc, st, ac, baseURL, candidatePath)
	}
	if !args.Recurse || br.ext == "" {
		return
	}
	res, err := fetch(hc, st, "HEAD", baseURL+candidatePath)
	if err != nil {
		log.WithFields(log.Fields{"err": err, "method": "HEAD", "url": baseURL + candidatePath}).Info("Directory recursion check error")
		return
	}
	if redirectsToDirectory(res, baseURL+candidatePath) {
		ac.autocompleteMutex.Lock()
		ac.foundDirectories[candidatePath] = struct{}{}
		ac.autocompleteMutex.Unlock()
	}
}

// redirectsToDirectory accepts absolute and relative Location values and
// ignores a redirect query string. Comparing parsed paths also handles escaped
// candidate names more reliably than a raw string suffix check.
func redirectsToDirectory(res *http.Response, candidateURL string) bool {
	if res == nil || res.Header.Get("Location") == "" {
		return false
	}
	location, err := res.Location()
	if err != nil {
		return false
	}
	candidate, err := nurl.Parse(candidateURL)
	if err != nil {
		return false
	}
	expectedPath := strings.TrimSuffix(candidate.Path, "/") + "/"
	return strings.EqualFold(location.Path, expectedPath)
}

func autocompleteProbeMethod(autocomplete string) string {
	switch autocomplete {
	case "method":
		return "_"
	case "allow-copy":
		return "PROPFIND"
	}
	return "GET"
}

// existsLikeStatus reports whether a status means "the resource exists but is
// protected or redirected" (auth walls, login redirects) rather than "missing".
func existsLikeStatus(status int) bool {
	switch status {
	case http.StatusMovedPermanently, http.StatusFound, http.StatusTemporaryRedirect,
		http.StatusPermanentRedirect, http.StatusUnauthorized, http.StatusForbidden:
		return true
	}
	return false
}

// statusEscalateSamples is how many EXTRA random-name probes are fetched to confirm
// an apparent status-differential hit before it is trusted (see
// statusExistsAgainstBaseline). Only spent on apparent hits, which are rare, so the
// extra cost is negligible against a scan's overall request volume.
const statusEscalateSamples = 10

// statusCacheKey builds the statusCache lookup key shared by escalateStatusBaseline
// and getStatusesForProbe. Both MUST derive the key the same way — escalate caches
// under this key, getStatusesForProbe reads it back — so an edit to one side that
// isn't mirrored in the other would silently desync the escalated baseline from the
// one later checked, defeating the differential-status false-positive guard
// (see statusExistsAgainstBaseline) with no error and no obvious symptom.
func statusCacheKey(c wordlistRecord, br baseRequest, method, suffix string) string {
	return br.url + "\x00" + strings.ToUpper(method) + "\x00" + suffix + "\x00" + strings.ToLower(c.extension)
}

// escalateStatusBaseline grows the cached "missing file" status baseline for a key
// with more random-name probes and merges the result back into the cache.
func escalateStatusBaseline(c wordlistRecord, br baseRequest, hc *http.Client, st *httpStats, method, suffix string) map[int]struct{} {
	cacheKey := statusCacheKey(c, br, method, suffix)
	extra := make(map[int]struct{}, statusEscalateSamples)
	for i := 0; i < statusEscalateSamples; i++ {
		p := randPath(rand.Intn(4)+8, 0, alphanum) + c.extension
		if res, err := fetchStatus(hc, st, method, br.url+p+suffix); err == nil {
			extra[res.StatusCode] = struct{}{}
		}
	}
	cacheMutex.Lock()
	// Build a NEW map (copy existing + extras) rather than mutating the cached one
	// in place: getStatusesForProbe hands the cached map out by reference to the
	// concurrent enumerate() workers, which read it WITHOUT the lock (the
	// --probe-candidates brute path at recoverLongName has no autocompleteMutex
	// held). Mutating it here would be a concurrent map read/write — a fatal,
	// recover()-proof Go throw that kills the whole scan. A fresh map keeps every
	// cached map immutable after insertion, so those lock-free reads stay safe.
	existing := statusCache[cacheKey]
	merged := make(map[int]struct{}, len(existing)+len(extra))
	for k := range existing {
		merged[k] = struct{}{}
	}
	for k := range extra {
		merged[k] = struct{}{}
	}
	statusCache[cacheKey] = merged
	cacheMutex.Unlock()
	log.WithFields(log.Fields{"extension": c.extension, "method": method, "suffix": suffix, "statuses": merged}).Debug("Escalated non-existent file status baseline")
	return merged
}

// statusExistsAgainstBaseline reports whether `status` indicates the candidate
// exists, by differential against a "genuinely missing" status baseline. The
// default baseline is cheap (2 random-name probes) so the common true-negative
// path stays fast; but 2 samples can miss a status value that an unstable server,
// or one that filters an unusual extension inconsistently, also returns for
// missing files — which otherwise reports a false "exists" positive. Confirmed
// live: a `.PUBLISHPROJ` candidate was reported as a match via the default 2-probe
// baseline, yet a manual request returned a plain 404 the small sample had missed.
// Before trusting an apparent hit (status absent from the small baseline), the
// baseline is escalated with more probes and the hit must still stand.
func statusExistsAgainstBaseline(c wordlistRecord, br baseRequest, hc *http.Client, st *httpStats, method, suffix string, status int) bool {
	if isTransientInfraStatus(status) {
		return false
	}
	statuses := getStatusesForProbe(c, br, hc, st, method, suffix)
	if len(statuses) == 0 {
		return false
	}
	for code := range statuses {
		if isTransientInfraStatus(code) {
			return false
		}
	}
	if _, seen := statuses[status]; seen {
		return false
	}
	escalated := escalateStatusBaseline(c, br, hc, st, method, suffix)
	for code := range escalated {
		if isTransientInfraStatus(code) {
			return false
		}
	}
	_, stillMissing := escalated[status]
	return !stillMissing
}

func probeAutocompleteCandidate(hc *http.Client, st *httpStats, ac *attackConfig, br baseRequest, baseURL string, candidate filenameCandidate) (*http.Response, bool, error) {
	// allow-copy oracle: the WebDAV method-capability differential (PROPFIND
	// Depth:0 -> 405 with COPY promoted into Allow for an existing resource) is its
	// own existence signal with its own paired controls, so it bypasses the generic
	// status/method/distance fetch entirely.
	if ac.autocomplete == "allow-copy" {
		candidatePath := pathEscape(candidate.record.filename + candidate.record.extension)
		return allowCopyExistsAgainstBaseline(hc, st, baseURL, candidatePath, "", candidate.record.extension)
	}
	method := autocompleteProbeMethod(ac.autocomplete)
	candidatePath := pathEscape(candidate.record.filename + candidate.record.extension)
	var res *http.Response
	var body []byte
	var err error
	if ac.autocomplete == "distance" {
		res, body, err = fetchBody(hc, st, method, baseURL+candidatePath, 1024)
	} else {
		res, err = fetchStatus(hc, st, method, baseURL+candidatePath)
	}
	if err != nil {
		return nil, false, err
	}
	if isTransientInfraStatus(res.StatusCode) {
		return res, false, nil
	}
	matched := false
	switch ac.autocomplete {
	case "method":
		// Invalid-method 405 means "this resource exists" — but only when it is
		// DISTINCTIVE. Some servers/WAFs, and ASP.NET extensionless routing, answer
		// 405 to the invalid method for anything, which would confirm every wordlist
		// guess (the recovered-name-that-GETs-404 false positives). Require the 405 to
		// differ from a same-extension baseline probed the same way. The baseline is
		// per-extension, so a requestFiltering-hidden file (GET 404, `_` 405) is still
		// recovered wherever the 405 signal is real, and only rejected in the exact
		// dimension where the host is 405-for-everything — the best of both worlds
		// without the blunt whole-oracle downgrade.
		probeRequest := br
		probeRequest.url = baseURL
		if res.StatusCode == http.StatusMethodNotAllowed {
			matched = statusExistsAgainstBaseline(candidate.record, probeRequest, hc, st, method, "", res.StatusCode)
			// 405 wasn't distinctive (405-happy in this dimension): a genuinely
			// served or auth-walled file still betrays itself with a distinctive GET
			// status, so fall back to that instead of trusting the meaningless 405.
			if !matched {
				if gres, gerr := fetchStatus(hc, st, "GET", baseURL+candidatePath); gerr == nil && existsLikeStatus(gres.StatusCode) {
					matched = statusExistsAgainstBaseline(candidate.record, probeRequest, hc, st, "GET", "", gres.StatusCode)
				}
			}
		} else if existsLikeStatus(res.StatusCode) {
			// Auth-gated / redirecting endpoints (301/302/307/308/401/403) exist but
			// don't answer 405 — method-magic alone silently drops them (exactly the
			// admin endpoints that matter). Confirm them against the same-method
			// baseline so they're recovered without catch-all false positives.
			matched = statusExistsAgainstBaseline(candidate.record, probeRequest, hc, st, method, "", res.StatusCode)
		}
	case "status":
		probeRequest := br
		probeRequest.url = baseURL
		matched = statusExistsAgainstBaseline(candidate.record, probeRequest, hc, st, method, "", res.StatusCode)
	case "distance":
		probeRequest := br
		probeRequest.url = baseURL
		dists := getDistances(candidate.record, probeRequest, hc, st, ac)
		var distance, delta float32
		matched, distance, delta = differsFromDistanceBaseline(res.StatusCode, body, dists)
		if matched {
			log.WithFields(log.Fields{"url": baseURL + candidatePath, "status": res.StatusCode, "distance": distance, "delta": delta}).Info("Autocomplete got a response-distance hit")
		}
	}
	return res, matched, nil
}

// recoverLongName either runs normal autocomplete or, when requested, probes
// every candidate with GET. Candidate export is independent of probing, so the
// resulting URL file can be handed directly to another HTTP tool.
// displayStatus returns the HTTP status to show next to a confirmed long name. The
// method-magic oracle ("_") answers 405 for every resource that exists — that means
// "exists", not how the resource actually responds — so re-fetch the real GET status
// (200, or a genuine 401/403/302) for the display column. Every other oracle already
// probes with a real method, so its status is meaningful and used unchanged.
func displayStatus(hc *http.Client, st *httpStats, autocomplete, method, url string, probeStatus int) int {
	// The method-magic ("_") and allow-copy oracles both answer with an existence
	// signal (405), not the resource's real status — re-GET for the display column.
	if method != "_" && autocomplete != "allow-copy" {
		return probeStatus
	}
	if res, err := fetchStatus(hc, st, "GET", url); err == nil {
		return res.StatusCode
	}
	return probeStatus
}

func recoverLongName(hc *http.Client, st *httpStats, ac *attackConfig, br baseRequest) recoveryMatch {
	observeRecoveryAlias(ac, br)
	selected := shortNameSelected(br)
	if ac.autocomplete == "none" && !(args.ProbeCandidates && selected) && !(candidateOutputWriter != nil && selected) {
		return recoveryMatch{}
	}
	includeKnown := args.KnownExtensions || (args.ProbeCandidates && selected) || (candidateOutputWriter != nil && selected)
	candidates := filenameCandidates(ac, br, includeKnown)
	baseURL := recoveryBaseURL(br)
	if candidateOutputWriter != nil && selected {
		for _, candidate := range candidates {
			emitCandidateURL(baseURL + pathEscape(candidate.record.filename+candidate.record.extension))
		}
	}

	// A protected-folder INDEX_ALLOCATION scan cannot normally verify an LFN at
	// baseURL: the candidate is still inside the ADS namespace.  Where aggressive
	// cookieless path removal is active, use a bodyless split-join HEAD oracle
	// instead.  This both recovers the full name and proves the content-read chain;
	// the later source auto-chain performs the only GET.
	if args.Index || args.Auto || args.Full {
		for _, candidate := range candidates {
			candidatePath := pathEscape(candidate.record.filename + candidate.record.extension)
			ac.autocompleteMutex.Lock()
			_, exists := ac.foundFiles[foundFileKey(candidatePath)]
			ac.autocompleteMutex.Unlock()
			if exists {
				continue
			}
			sourceMatch, err := probeSourceSplitCandidate(hc, st, br.url, candidatePath)
			if err != nil {
				log.WithFields(log.Fields{"err": err, "method": http.MethodHead, "candidate": candidatePath}).Info("Source-split existence check error")
				continue
			}
			if sourceMatch.workingURL == "" {
				continue
			}
			ac.autocompleteMutex.Lock()
			rememberConfirmedStem(ac, br, candidate, sourceMatch.baseURL)
			markResolvedFile(ac, br, sourceMatch.baseURL, candidatePath)
			ac.autocompleteMutex.Unlock()
			enrichResolvedFile(hc, st, ac, br, sourceMatch.baseURL, candidatePath)
			return recoveryMatch{
				path: candidatePath, baseURL: sourceMatch.baseURL, matchType: candidate.matchType,
				status: sourceMatch.status, collisionGroup: shortCollisionGroup(br),
				ordinalVerified: candidateVerifiesOrdinal(br, candidatePath),
				oracle:          "source-split", method: http.MethodHead,
				checksum: candidate.checksum, derivedFrom: candidate.source, families: candidate.families,
			}
		}
	}

	if args.ProbeCandidates && selected {
		group := shortCollisionGroup(br)
		bruteOracle := strings.ToLower(args.ProbeOracle)
		if bruteOracle == "" {
			bruteOracle = "status"
		}
		bruteMethod := strings.ToUpper(args.ProbeMethod)
		if bruteMethod == "" {
			bruteMethod = "GET"
		}
		if bruteOracle == "allow-copy" {
			bruteMethod = "PROPFIND"
		} else if bruteOracle == "translate" {
			bruteMethod = "GET"
		}
		bodyLimit := int64(args.ProbeBodyLimit)
		if bodyLimit <= 0 {
			bodyLimit = 4096
		}
		groupKey := strings.ToLower(baseURL + "\x00" + br.file + "\x00" + br.ext)
		ac.autocompleteMutex.Lock()
		if ac.bruteGroups == nil {
			ac.bruteGroups = make(map[string]struct{})
		}
		_, groupAlreadyProcessed := ac.bruteGroups[groupKey]
		if !groupAlreadyProcessed {
			ac.bruteGroups[groupKey] = struct{}{}
		}
		ac.autocompleteMutex.Unlock()

		var first recoveryMatch
		for _, candidate := range candidates {
			// Literal short-alias candidates differ by ordinal and therefore need
			// one probe per observed alias. Long-name candidates are common to the
			// whole six-character collision group and are probed only once.
			if groupAlreadyProcessed && !strings.HasPrefix(candidate.matchType, "short-name") {
				continue
			}
			candidatePath := pathEscape(candidate.record.filename + candidate.record.extension)
			probeURL := baseURL + candidatePath + args.ProbeSuffix
			var res *http.Response
			var body []byte
			var err error
			allowCopyMatched := false
			translateMatched := false
			if bruteOracle == "allow-copy" {
				res, allowCopyMatched, err = allowCopyExistsAgainstBaseline(hc, st, baseURL, candidatePath, args.ProbeSuffix, candidate.record.extension)
				if err != nil {
					log.WithFields(log.Fields{"err": err, "method": bruteMethod, "url": probeURL}).Info("Brute-force Allow/COPY check error")
					continue
				}
				if !allowCopyMatched {
					continue
				}
			} else if bruteOracle == "translate" {
				res, translateMatched, err = translateExistsAgainstBaseline(hc, st, baseURL, candidatePath, args.ProbeSuffix, candidate.record.extension)
				if err != nil {
					log.WithFields(log.Fields{"err": err, "method": bruteMethod, "url": probeURL}).Info("Brute-force Translate check error")
					continue
				}
				if !translateMatched {
					continue
				}
			} else if bruteOracle == "distance" {
				res, body, err = fetchBody(hc, st, bruteMethod, probeURL, bodyLimit)
			} else {
				res, err = fetchStatus(hc, st, bruteMethod, probeURL)
			}
			if err != nil {
				log.WithFields(log.Fields{"err": err, "method": bruteMethod, "url": probeURL}).Info("Brute-force check error")
				continue
			}
			_, accepted := bruteStatuses[res.StatusCode]
			if bruteOracle != "allow-copy" && bruteOracle != "translate" && !accepted {
				continue
			}
			probeRequest := br
			probeRequest.url = baseURL
			matched := false
			if bruteOracle == "allow-copy" {
				matched = allowCopyMatched
			} else if bruteOracle == "translate" {
				matched = translateMatched
			} else if bruteOracle == "distance" {
				dists := getDistancesForProbe(candidate.record, probeRequest, hc, st, ac, bruteMethod, args.ProbeSuffix, bodyLimit)
				var distance, delta float32
				matched, distance, delta = differsFromDistanceBaseline(res.StatusCode, body, dists)
				if matched {
					log.WithFields(log.Fields{"url": probeURL, "status": res.StatusCode, "distance": distance, "delta": delta}).Info("Brute-force got a response-distance hit")
				}
			} else {
				matched = statusExistsAgainstBaseline(candidate.record, probeRequest, hc, st, bruteMethod, args.ProbeSuffix, res.StatusCode)
			}
			if matched {
				ac.autocompleteMutex.Lock()
				_, alreadyFound := ac.foundFiles[foundFileKey(candidatePath)]
				if !alreadyFound {
					rememberConfirmedStem(ac, br, candidate, baseURL)
					markResolvedFile(ac, br, baseURL, candidatePath)
				}
				ac.autocompleteMutex.Unlock()
				if !alreadyFound {
					enrichResolvedFile(hc, st, ac, br, baseURL, candidatePath)
				}
				verified := candidateVerifiesOrdinal(br, candidatePath)
				match := recoveryMatch{
					path: candidatePath, baseURL: baseURL, matchType: candidate.matchType,
					status: res.StatusCode, collisionGroup: group, ordinalVerified: verified,
					oracle: bruteOracle, method: bruteMethod, suffix: args.ProbeSuffix,
					checksum: candidate.checksum, derivedFrom: candidate.source, families: candidate.families,
				}
				if first.path == "" {
					first = match
				}
				if args.Output == "human" {
					ordinal := "ordinal unverified"
					if verified {
						ordinal = "exact alias path"
					}
					profile := bruteOracle + "/" + bruteMethod
					if args.ProbeSuffix != "" {
						profile += " suffix=" + strconv.Quote(args.ProbeSuffix)
					}
					if candidate.checksum != "" {
						profile += "; ck=" + candidate.checksum
						if len(candidate.families) > 0 {
							profile += " families=" + strings.Join(candidate.families, ",")
						}
						if candidate.source != "" {
							profile += " from " + candidate.source
						}
					}
					ac.emitHuman(fmt.Sprintf("  %s %s -> %s (%s; %s; %s; status %d)", color.HiGreenString("[BRUTE]"), group, color.HiGreenString(baseURL+candidatePath), candidate.matchType, profile, ordinal, res.StatusCode))
				} else {
					printJSON(resultOutput{
						Type: "recovery", FullMatch: true, BaseUrl: baseURL,
						File: br.file, Tilde: br.tilde, Ext: br.ext, Fullname: candidatePath,
						MatchType: candidate.matchType, Status: res.StatusCode,
						CollisionGroup: group, OrdinalVerified: boolPointer(verified),
						Oracle: bruteOracle, Method: bruteMethod, ProbeSuffix: args.ProbeSuffix,
						Checksum: candidate.checksum, DerivedFrom: candidate.source, CandidateFamilies: candidate.families,
					})
				}
			}
		}
		// A bare --probe-candidates is a single specialized brute — return its result
		// verbatim (probing each candidate exactly once). But --full runs it as an
		// EXTRA pass on top of the method-oracle resolution, so when the brute resolves
		// nothing — its status oracle can't match a 301/302 directory (app_themes,
		// aspnet_client, …) and it never reaches the request-filtered inference
		// (web.config, global.asax) — fall through to the method-oracle verification +
		// inference below, so --full is never WORSE than --auto (the reported bug).
		if first.path != "" || !args.Full {
			return first
		}
	}

	if ac.autocomplete == "none" {
		return recoveryMatch{}
	}
	method := autocompleteProbeMethod(ac.autocomplete)
	for _, candidate := range candidates {
		candidatePath := pathEscape(candidate.record.filename + candidate.record.extension)
		ac.autocompleteMutex.Lock()
		if _, exists := ac.foundFiles[foundFileKey(candidatePath)]; exists {
			ac.autocompleteMutex.Unlock()
			continue
		}
		// Unlocked across the network round-trip: recoverLongName is called once
		// per short name from enumerate()'s concurrent workers (up to -c of them),
		// and holding this lock through probeAutocompleteCandidate here used to
		// serialize every one of those workers behind whichever one was mid-probe
		// — for EVERY candidate, not just confirmed matches. See enrichResolvedFile's
		// doc comment for the same pattern applied to a match's own follow-up calls.
		ac.autocompleteMutex.Unlock()
		res, matched, err := probeAutocompleteCandidate(hc, st, ac, br, baseURL, candidate)
		if err != nil {
			log.WithFields(log.Fields{"err": err, "method": method, "url": baseURL + candidatePath}).Info("Existence check error")
			continue
		}
		if matched {
			// Re-check under lock before marking: two candidates (from this or
			// another concurrent recoverLongName call) can independently resolve
			// the same path; only the first to arrive here should record it.
			ac.autocompleteMutex.Lock()
			if _, exists := ac.foundFiles[foundFileKey(candidatePath)]; exists {
				ac.autocompleteMutex.Unlock()
				continue
			}
			rememberConfirmedStem(ac, br, candidate, baseURL)
			markResolvedFile(ac, br, baseURL, candidatePath)
			ac.autocompleteMutex.Unlock()
			enrichResolvedFile(hc, st, ac, br, baseURL, candidatePath)
			return recoveryMatch{
				path: candidatePath, baseURL: baseURL, matchType: candidate.matchType,
				status: displayStatus(hc, st, ac.autocomplete, method, baseURL+candidatePath, res.StatusCode), collisionGroup: shortCollisionGroup(br),
				ordinalVerified: candidateVerifiesOrdinal(br, candidatePath),
				oracle:          ac.autocomplete, method: method,
				checksum: candidate.checksum, derivedFrom: candidate.source, families: candidate.families,
			}
		}
	}

	// Request-filtered inference: web.config and friends enumerate by their 8.3
	// alias but IIS hides the LONG name (404.8 hidden-segment / 403 denied
	// extension), so no GET can ever confirm the candidate above and it would drop
	// to an unresolved WEB.CON?. When a wordlist candidate whose 8.3 matches this
	// alias is such an always-hidden name, surface it as an INFERENCE — clearly
	// marked, never HTTP-confirmed, never counted toward the resolved tally.
	if ac.autocomplete != "none" {
		for _, candidate := range candidates {
			if candidate.matchType != "wordlist" && candidate.matchType != "framework-manifest" {
				continue
			}
			name := candidate.record.filename + candidate.record.extension
			if !isRequestFilteredName(name) {
				continue
			}
			rememberInferredStem(ac, br, candidate, baseURL)
			return recoveryMatch{
				path: pathEscape(name), baseURL: baseURL, matchType: "wordlist-inferred",
				collisionGroup: shortCollisionGroup(br), ordinalVerified: false,
				oracle: ac.autocomplete, derivedFrom: candidate.source,
			}
		}
	}
	return recoveryMatch{}
}

// requestFilteredExtensions mirrors the file extensions a DEFAULT IIS install
// refuses a direct GET for even though the 8.3 alias still enumerates: the
// applicationHost.config <requestFiltering><fileExtensions> deny list plus the
// ASP.NET root-web.config extensions mapped to HttpForbiddenHandler ("this type
// of page is not served"). Source, project, license, compiled-marker, class
// diagram and App_Data database files — all high-value for disclosure, none
// GET-confirmable. Served handler extensions (.aspx/.asmx/.ashx/.axd/.svc/.rem/
// .soap) are deliberately ABSENT: those answer a GET and are confirmed normally.
// Marking one here only ever adds an INFERENCE, and only as a last resort after
// the method-oracle GET-confirm already failed for every candidate (a name that
// actually serves is confirmed before the inference is ever reached), so a stray
// entry cannot manufacture a false "served" result.
var requestFilteredExtensions = []string{
	// IIS default <fileExtensions> deny list (applicationHost.config).
	".asax", ".ascx", ".master", ".skin", ".browser", ".sitemap",
	".config", ".cs", ".csproj", ".vb", ".vbproj", ".webinfo",
	".licx", ".resx", ".resources", ".mdb", ".vjsproj", ".java",
	".jsl", ".ldb", ".dsdgm", ".ssdgm", ".lsad", ".ssmap", ".cd",
	".dsprototype", ".lsaprototype", ".sdm", ".sdmdocument",
	".mdf", ".ldf", ".ad", ".dd", ".ldd", ".sld", ".cnf",
	// ASP.NET HttpForbiddenHandler extras (GET-refused, high disclosure value).
	".compiled", ".exclude", ".refresh",
}

// isRequestFilteredName reports whether IIS's default Request Filtering hides the
// LONG name (hiddenSegments / denied fileExtensions) so a GET can never confirm it
// even though the 8.3 alias enumerates. Drives the wordlist-inferred fallback.
func isRequestFilteredName(name string) bool {
	n := strings.ToLower(name)
	if i := strings.LastIndexAny(n, "/\\"); i >= 0 {
		n = n[i+1:]
	}
	if n == "web.config" || n == "global.asax" {
		return true
	}
	for _, ext := range requestFilteredExtensions {
		if strings.HasSuffix(n, ext) {
			return true
		}
	}
	return false
}

// inspectResolvedFile fetches at most 4 KiB from a confirmed file and inspects
// it for source/binary disclosure signatures.
func inspectResolvedFile(hc *http.Client, st *httpStats, ac *attackConfig, br baseRequest, fnr string) {
	if !args.InspectSource {
		return
	}
	res, body, err := fetchBody(hc, st, "GET", br.url+fnr, 4096)
	if err != nil {
		return
	}
	if res.StatusCode < 200 || res.StatusCode >= 300 {
		return
	}
	if len(body) == 0 {
		return
	}
	disc, dt := inspectDisclosure(body)
	if !disc {
		return
	}
	if args.Output == "human" {
		// Full URL, not just the name, and routed through ac.emitHuman so it lands in
		// the right host's block under --parallel (workers can't reach the sink).
		ac.emitHuman(fmt.Sprintf("  %s %s (%s)", color.HiRedString("[!] Source disclosure:"), color.HiYellowString(br.url+fnr), dt))
	} else {
		printJSON(resultOutput{
			Type: "disclosure", FullMatch: true, SourceDisclosure: true, DisclosureType: dt,
			BaseUrl: br.url, File: br.file, Tilde: br.tilde, Ext: br.ext, Fullname: fnr,
		})
	}
}

// mutateExtensions are common backup/source-leak suffixes appended after a hit when --mutate-ext
var mutateExtensions = []string{".bak", ".old", ".orig", ".swp", ".txt", "~", ".disabled", ".1", ".copy", ".save"}

// probeMutations tests common backup/source-leak suffixes after the autocomplete confirmed `fnr`.
// Reports any hit with the same source-disclosure heuristics as the main path.
func probeMutations(hc *http.Client, st *httpStats, ac *attackConfig, baseUrl, fnr string) {
	if !args.MutateExt {
		return
	}
	// Catch-all guard: if an impossible same-stem sibling also serves 2xx with a
	// body, this path answers 200 to everything (soft-404 / serve-everything front
	// end), so every backup-suffix probe below would be a false "mutation hit".
	// Probe one deliberately non-existent extension and bail if it serves.
	if cres, cbody, _ := fetchBody(hc, st, "GET", baseUrl+fnr+"."+randAlnum(8), 2048); cres != nil && cres.StatusCode/100 == 2 && len(cbody) > 0 {
		return
	}
	for _, suf := range mutateExtensions {
		candidate := fnr + suf
		res, body, err := fetchBody(hc, st, "GET", baseUrl+candidate, 4096)
		if err != nil || res.StatusCode < 200 || res.StatusCode >= 300 {
			continue
		}
		disc, dt := inspectDisclosure(body)
		label := "[mutation hit]"
		if disc {
			label = "[!] mutation + disclosure (" + dt + ")"
		}
		if args.Output == "human" {
			// Full URL (host + path), routed through ac.emitHuman so it lands in the
			// right host's block under --parallel (workers can't reach the sink).
			ac.emitHuman(fmt.Sprintf("  %s %s", color.HiYellowString(label), color.HiGreenString(baseUrl+candidate)))
		} else {
			printJSON(resultOutput{
				Type: "mutation", FullMatch: true, SourceDisclosure: disc, DisclosureType: dt,
				BaseUrl: baseUrl, Fullname: candidate,
			})
		}
	}
}

// testIndexAllocations tests special paths such as ::$INDEX_ALLOCATION.
// Tries the canonical form first; only falls back to NTFS ADS variants if
// the canonical form did not yield a vulnerable result (the server may have
// case-sensitive filtering or a WAF rule on the literal string).
func testIndexAllocations(urls []string, hc *http.Client, st *httpStats, wc *wordlistConfig, mk markers) {
	paths := []string{
		"::$INDEX_ALLOCATION",
		"::$index_allocation",
		":$i30:$INDEX_ALLOCATION",
		":$I30:$INDEX_ALLOCATION",
		"::$DATA",
	}
	for _, url := range urls {
		url = strings.TrimSuffix(url, "/")

		parsedURL, err := nurl.Parse(url)
		if err != nil {
			log.WithFields(log.Fields{"url": url, "error": err}).Error("Unable to parse URL")
			continue
		}
		// `name::$INDEX_ALLOCATION` needs a NAMED directory segment to suffix — the
		// site root has none (it's the origin, not a name inside a parent), so the
		// ADS trick doesn't syntactically apply to it. A bare root's own 8.3 names
		// (global.asax, web.config, packages.config, …) are files sitting directly
		// in it and are already reachable through the PLAIN tilde oracle, no ADS
		// needed. Silently substituting "/bin" here used to guess a target behind
		// the user's back — confusing on a live scan (a "wtf?" moment), and wrong
		// whenever the real target was a different reserved folder (App_Code,
		// App_Data, Views, …) or the user genuinely just wanted -i to no-op on a
		// root that has nothing to test. Say so instead and point at the sweep that
		// actually covers every reserved folder from the root: --auto -i / --full -i.
		if parsedURL.Path == "" || parsedURL.Path == "/" {
			printHuman(color.HiYellowString("-i: %q is a bare site root — ::$INDEX_ALLOCATION needs a named directory to suffix (e.g. %s/bin), so there is nothing to test here directly. Point -i at a specific reserved folder, or combine with --auto/--full to sweep all of them (/bin, App_Code, App_Data, Views, Models, Controllers, …) from the root.", url, strings.TrimSuffix(url, "/")))
			continue
		}

		for i, p := range paths {
			before := vulnerableCount
			Scan([]string{url + p}, hc, st, wc, mk, make(map[string]struct{}))
			if vulnerableCount > before {
				if i > 0 {
					log.WithFields(log.Fields{"variant": p}).Info("ADS fallback variant succeeded")
				}
				break
			}
			log.WithFields(log.Fields{"variant": p}).Debug("Variant did not produce results, trying next")
		}
	}
}

// filenameCandidates returns deterministic, de-duplicated long-name
// candidates. Exact rainbow/plain matches take precedence over candidates made
// by combining a matching filename stem with a well-known extension.
func filenameCandidates(ac *attackConfig, br baseRequest, includeKnownExtensions bool) []filenameCandidate {
	shortExtension := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
	candidates := make(map[string]filenameCandidate)
	addCandidate := func(candidate filenameCandidate) {
		record := candidate.record
		key := strings.ToLower(record.filename + record.extension)
		if _, exists := candidates[key]; exists {
			return
		}
		candidates[key] = candidate
	}
	add := func(record wordlistRecord, matchType string) {
		addCandidate(filenameCandidate{record: record, matchType: matchType})
	}
	for _, candidate := range referenceFilenameCandidates(ac, br) {
		addCandidate(candidate)
	}
	for _, candidate := range siblingFilenameCandidates(ac, br, includeKnownExtensions) {
		addCandidate(candidate)
	}
	for _, candidate := range checksumMaskCandidates(br) {
		addCandidate(candidate)
	}
	for _, candidate := range frameworkManifestCandidates(br) {
		addCandidate(candidate)
	}
	if includeKnownExtensions && br.file != "" && br.tilde != "" && shortExtension != "" {
		shortStem := br.file + br.tilde
		add(wordlistRecord{filename: shortStem, extension: br.ext, extension83: shortExtension}, "short-name")
		for _, extension := range wellKnownExtensions {
			_, _, extension83 := shortutil.Gen8dot3("x", extension)
			if strings.EqualFold(extension83, shortExtension) {
				add(wordlistRecord{filename: shortStem, extension: extension, extension83: extension83}, "short-name-known-extension")
			}
		}
	}

	var isRainbow bool
	if ac.wordlist != nil {
		// records() also waits for the deferred load to finish (waitLoaded()) — that
		// synchronization still has to happen here even though the candidate lookups
		// below go through the indexed accessors, not this slice.
		_, isRainbow = ac.wordlist.records()
	}

	upperFile := strings.ToUpper(br.file)
	if isRainbow && checksumRegex != nil && checksumRegex.MatchString(upperFile) && len(upperFile) >= 5 {
		prefixLength := len(upperFile) - 4
		prefix, checksum := upperFile[:prefixLength], upperFile[prefixLength:]
		log.WithFields(log.Fields{"file": br.file, "prefix": prefix, "checksum": checksum}).Info("Possible checksummed alias")
		// Bucketed by first char instead of a full wordlist scan (checksummed prefixes
		// are always 1-2 chars, so this cuts the candidate set to ~1/36th on average);
		// still applies the real HasPrefix check per candidate in the bucket.
		for _, record := range ac.wordlist.candidatesByPrefixBucket(prefix) {
			if !strings.HasPrefix(strings.ToUpper(record.filename), prefix) ||
				!strings.HasPrefix(strings.ToUpper(record.extension), strings.ToUpper(br.ext)) {
				continue
			}
			for offset := 0; offset+4 <= len(record.checksums); offset += 4 {
				if strings.EqualFold(record.checksums[offset:offset+4], checksum) {
					add(record, "checksum")
					break
				}
			}
		}
	}

	// Indexed by 8.3 base instead of a full wordlist scan: this runs for EVERY
	// resolved short name, so on the embedded 111k-line default wordlist this was the
	// dominant recovery-phase cost on a directory with many resolved aliases.
	for _, record := range ac.wordlist.candidatesByFilename83(br.file) {
		if strings.EqualFold(shortExtension, record.extension83) {
			add(record, "wordlist")
		}
	}

	if includeKnownExtensions && shortExtension != "" {
		seenStems := make(map[string]struct{})
		for _, record := range ac.wordlist.candidatesByFilename83(br.file) {
			stemKey := strings.ToLower(record.filename)
			if _, exists := seenStems[stemKey]; exists {
				continue
			}
			seenStems[stemKey] = struct{}{}
			for _, extension := range wellKnownExtensions {
				_, filename83, extension83 := shortutil.Gen8dot3(record.filename, extension)
				if strings.EqualFold(filename83, br.file) && strings.EqualFold(extension83, shortExtension) {
					add(wordlistRecord{
						filename: record.filename, extension: extension,
						filename83: filename83, extension83: extension83,
					}, "well-known-extension")
				}
			}
		}
	}

	// Complete-short-base recovery: an 8.3 base is truncated only when the long base is
	// longer than the 8.3 base, and truncation always fills all 6 base characters — so a
	// short name whose base is shorter than 6 characters (WEB, STR, DATA) is the COMPLETE
	// base, and even a 6-character base is often complete (report, global, config). Try the
	// bare base + every well-known extension whose 8.3 form matches the observed extension.
	// Every candidate is HTTP-verified downstream, so a truncated 6-char base simply fails to
	// confirm; this recovers short-base + long-extension files (web.config, data.json,
	// home.xhtml, config.json) with no wordlist entry for them.
	if includeKnownExtensions && br.file != "" && shortExtension != "" {
		base := strings.ToLower(br.file)
		for _, extension := range wellKnownExtensions {
			_, filename83, extension83 := shortutil.Gen8dot3(base, extension)
			if strings.EqualFold(filename83, br.file) && strings.EqualFold(extension83, shortExtension) {
				add(wordlistRecord{
					filename: base, extension: extension,
					filename83: filename83, extension83: extension83,
				}, "short-base-known-extension")
			}
		}
	}

	result := make([]filenameCandidate, 0, len(candidates))
	for _, candidate := range candidates {
		result = append(result, candidate)
	}
	sort.Slice(result, func(i, j int) bool {
		leftReference := result[i].matchType == "reference"
		rightReference := result[j].matchType == "reference"
		if leftReference != rightReference {
			return leftReference
		}
		leftSibling := result[i].matchType == "sibling-stem"
		rightSibling := result[j].matchType == "sibling-stem"
		if leftSibling != rightSibling {
			return leftSibling
		}
		leftManifest := result[i].matchType == "framework-manifest"
		rightManifest := result[j].matchType == "framework-manifest"
		if leftManifest != rightManifest {
			return leftManifest
		}
		left := strings.ToLower(result[i].record.filename + result[i].record.extension)
		right := strings.ToLower(result[j].record.filename + result[j].record.extension)
		return left < right
	})
	if len(result) > 0 {
		log.WithFields(log.Fields{"file": br.file, "ext": br.ext, "count": len(result)}).Info("Long-name recovery found candidates")
		log.WithFields(log.Fields{"candidates": result}).Trace("Long-name candidates")
	}
	return result
}

func getStatusesForProbe(c wordlistRecord, br baseRequest, hc *http.Client, st *httpStats, method, suffix string) map[int]struct{} {
	cacheKey := statusCacheKey(c, br, method, suffix)
	cacheMutex.RLock()
	cached := statusCache[cacheKey]
	cacheMutex.RUnlock()
	if len(cached) > 0 {
		return cached
	}
	l := 2
	if args.Stabilise {
		l = 12
	}
	statuses := make(map[int]struct{}, l)
	for i := 0; i < l; i++ {
		p := randPath(rand.Intn(4)+8, 0, alphanum) + c.extension
		if res, err := fetchStatus(hc, st, method, br.url+p+suffix); err == nil {
			statuses[res.StatusCode] = struct{}{}
		}
	}
	log.WithFields(log.Fields{"extension": c.extension, "method": method, "suffix": suffix, "statuses": statuses}).Info("Got non-existent file statuses")
	cacheMutex.Lock()
	statusCache[cacheKey] = statuses
	cacheMutex.Unlock()
	return statuses
}

// getDistances calculates response distances using Levenshtein
func getDistances(c wordlistRecord, br baseRequest, hc *http.Client, st *httpStats, ac *attackConfig) map[int]distances {
	return getDistancesForProbe(c, br, hc, st, ac, "GET", "", 1024)
}

func getDistancesForProbe(c wordlistRecord, br baseRequest, hc *http.Client, st *httpStats, ac *attackConfig, method, suffix string, bodyLimit int64) map[int]distances {
	ac.distanceMutex.Lock()
	defer ac.distanceMutex.Unlock()
	cacheKey := br.url + "\x00" + strings.ToUpper(method) + "\x00" + suffix + "\x00" + strconv.FormatInt(bodyLimit, 10) + "\x00" + strings.ToLower(c.extension)
	cacheMutex.RLock()
	cached := distanceCache[cacheKey]
	cacheMutex.RUnlock()
	if len(cached) > 0 {
		return cached
	}
	log.WithFields(log.Fields{"url": br.url, "extension": c.extension, "method": method, "suffix": suffix}).Info("Sampling responses for Levenshtein distance calculation")
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
		if res, bodyBytes, err := fetchBody(hc, st, method, br.url+p+suffix, bodyLimit); err == nil {
			body := string(bodyBytes)
			for j := 0; j < len(bodies[res.StatusCode]); j++ {
				ld := levenshtein.Distance(bodies[res.StatusCode][j], body)
				denominator := maths.Max(len(bodies[res.StatusCode][j]), len(body))
				if denominator == 0 {
					continue
				}
				lp := float32(ld) / float32(denominator)
				if dists[res.StatusCode] == (distances{}) || lp > highdist[res.StatusCode] {
					dists[res.StatusCode] = distances{distance: lp, body: body}
					highdist[res.StatusCode] = lp
				}
			}
			bodies[res.StatusCode] = append(bodies[res.StatusCode], body)
		}
	}
	for status, samples := range bodies {
		if len(samples) == 0 {
			continue
		}
		baseline := dists[status]
		if baseline.body == "" {
			baseline.body = samples[0]
		}
		baseline.samples = len(samples)
		dists[status] = baseline
	}
	for s, d := range dists {
		log.WithFields(log.Fields{"extension": c.extension, "status": s, "distance": d.distance, "samples": d.samples}).Info("Calculated Levenshtein distance")
	}
	cacheMutex.Lock()
	distanceCache[cacheKey] = dists
	cacheMutex.Unlock()
	return dists
}

func differsFromDistanceBaseline(status int, body []byte, dists map[int]distances) (bool, float32, float32) {
	if isTransientInfraStatus(status) {
		return false, 0, 0
	}
	totalSamples := 0
	for code, baseline := range dists {
		if isTransientInfraStatus(code) {
			return false, 0, 0
		}
		totalSamples += baseline.samples
	}
	if totalSamples < 2 {
		return false, 0, 0
	}
	baseline, exists := dists[status]
	if !exists {
		return true, 1, 1
	}
	if baseline.samples < 2 {
		return false, 0, 0
	}
	denominator := maths.Max(len(baseline.body), len(body))
	if denominator == 0 {
		return false, 0, 0
	}
	distance := float32(levenshtein.Distance(baseline.body, string(body))) / float32(denominator)
	delta := distance - baseline.distance
	return delta > 0.1, distance, delta
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
