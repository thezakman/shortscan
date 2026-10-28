package shortscan

import (
	"fmt"
	"math/rand"
	"net/http"
	nurl "net/url"
	"os"
	"os/signal"
	"regexp"
	"runtime/debug"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/alexflint/go-arg"
	"github.com/fatih/color"
	"github.com/mattn/go-isatty"
	log "github.com/sirupsen/logrus"
	"github.com/thezakman/shortscan/pkg/hashrecover"
)

// Command-line arguments and help
type arguments struct {
	Urls              []string `arg:"positional" help:"url to scan (use @file.txt to load URLs from a file inline)" placeholder:"URL"`
	List              string   `arg:"--list,-l" help:"file containing list of URLs to scan" placeholder:"FILE"`
	Wordlists         []string `arg:"--wordlist,-w,separate" help:"combined wordlist + rainbow table generated with shortutil (repeatable)" placeholder:"FILE"`
	Headers           []string `arg:"--header,-H,separate" help:"header to send with each request (use multiple times for multiple headers)"`
	Concurrency       int      `arg:"-c" help:"number of requests to make at once" default:"20"`
	Timeout           int      `arg:"-t" help:"per-request timeout in seconds" placeholder:"SECONDS" default:"10"`
	Rate              float32  `arg:"--rate" help:"maximum requests per second (0 = unlimited; supports fractional values)" placeholder:"RPS" default:"0"`
	Parallel          int      `arg:"--parallel" help:"number of URLs to scan in parallel (all output modes). Output lines are serialised so nothing corrupts, but in human mode blocks from different hosts interleave line-by-line; set 1 to keep each host's block contiguous" placeholder:"N" default:"10"`
	MaxTime           int      `arg:"--maxtime" help:"soft time budget in seconds for each top-level URL's whole scan, INCLUDING its -r recursion, before it stops and moves on (0 = no limit, the default). Opt-in for bulk/--parallel runs so one slow or tarpit host can't stall the queue; when it trips it says how many queued paths it skipped. Leave at 0 for a normal recursive scan so nothing is silently dropped. In-flight requests are still bounded by -t" placeholder:"SECONDS" default:"0"`
	Proxy             string   `arg:"--proxy" help:"proxy URL (http://, https://, socks5://). Falls back to HTTP_PROXY env" placeholder:"URL"`
	ProxyAuth         string   `arg:"--proxy-auth" help:"proxy basic auth credentials in user:pass form" placeholder:"USER:PASS"`
	Insecure          bool     `arg:"--insecure,-k" help:"skip TLS certificate verification (currently default for compatibility)" default:"true"`
	TLSMin            string   `arg:"--tls-min" help:"minimum TLS version (1.0, 1.1, 1.2, 1.3)" placeholder:"VER" default:"1.0"`
	UserAgent         string   `arg:"--user-agent,-A" help:"custom User-Agent string" placeholder:"UA"`
	RandomAgent       bool     `arg:"--random-agent" help:"rotate User-Agent from a built-in pool per request" default:"false"`
	Cookies           []string `arg:"--cookie,-b,separate" help:"cookie name=value (repeatable)" placeholder:"NAME=VAL"`
	Retries           int      `arg:"--retries" help:"number of retries on transport error" default:"3"`
	RetryDelay        int      `arg:"--retry-delay" help:"base retry delay in milliseconds (exponential backoff, capped at 30s)" placeholder:"MS" default:"500"`
	HTTP2             bool     `arg:"--http2" help:"force HTTP/2 negotiation" default:"false"`
	TildeEncoding     string   `arg:"--tilde-encoding" help:"how to encode the ~ character (default|percent|unicode|double|iis-unicode|all)" placeholder:"MODE" default:"default"`
	SessionStyle      string   `arg:"--session-style" help:"cookieless session token style for $INDEX_ALLOCATION (d|x|f|a|empty|rand)" placeholder:"S" default:"d"`
	SessionEncoding   string   `arg:"--session-encoding" help:"cookieless token encoding for $INDEX_ALLOCATION (literal|outer|asymmetric|asymmetric-full)" placeholder:"MODE" default:"literal"`
	ExactShorts       []string `arg:"--exact-short,separate" help:"probe an exact 8.3 alias, including custom forms without ~N, with paired bodyless controls (repeatable; standalone mode)" placeholder:"SHORTNAME"`
	ExactProfile      string   `arg:"--exact-short-profile" help:"exact-alias probe profile (auto|direct|late|late-encoded)" placeholder:"MODE" default:"auto"`
	ExactMethod       string   `arg:"--exact-short-method" help:"read-only exact-alias method (auto|HEAD|OPTIONS|TRACE); auto tries them in that order per profile" placeholder:"METHOD" default:"auto"`
	ExactRepeats      int      `arg:"--exact-short-repeats" help:"repetitions required for a stable exact-alias differential" placeholder:"N" default:"2"`
	ExactAppRoot      string   `arg:"--exact-short-app-root" help:"ASP.NET application root used for late profiles" placeholder:"PATH" default:"/"`
	CustomSFN         []string `arg:"--custom-sfn,separate" help:"custom-SFN content READ (the read complement to --exact-short's existence probe): give a custom 8.3 alias WITHOUT ~<digit> (e.g. SRC47.TXT, RCFG~A.TXT, DATA47) plus a base URL; GETs it and, guarded by a random same-extension control, discloses + saves the request-filtered file/dir it resolves to. A non-~digit alias escapes iiscore!CheckIfShortFileName, whose 404.0 canonical-mismatch fires only on tilde+digit. The alias must PRE-EXIST (set via SetFileShortName; not remotely plantable) — feed names from dir /x, a deploy/backup manifest, or a foothold. Loot under --loot-dir. Standalone by default (one read against the given URL(s)); combined with --auto/--full/-r it additionally probes each alias at every scanned directory. Repeatable" placeholder:"SHORTNAME"`
	BitmapProfile     bool     `arg:"--bitmap-profile" help:"standalone read-only directory-index profile: use paired PROPFIND/Allow controls with ::$INDEX_ALLOCATION, ::$BITMAP and :$I30:$BITMAP to distinguish a resident index from one materialized now or historically; requires a WebDAV capability oracle" default:"false"`
	SiblingRecovery   bool     `arg:"--sibling-recovery" help:"reuse verified long stems across matching aliases/extensions and recursively scanned directories" default:"false"`
	CollisionAncestry bool     `arg:"--collision-ancestry" help:"link saturated PREFIX~1..~4 families to checksummed PPHHHH~N siblings and reconstruct long names by prefix+checksum (opt-in; HTTP-verified)" default:"false"`
	ChecksumMasks     []string `arg:"--checksum-mask,separate" help:"reconstruct hashed-alias long names from a mask (e.g. 'App_Web_????.dll' or 'App_Web_*.dll'); '?' = one --checksum-alphabet char, '*' = a variable-length run the tool iterates, fixed chars participate in the checksum (repeatable; HTTP-verified)" placeholder:"MASK"`
	ChecksumAlphabet  string   `arg:"--checksum-alphabet" help:"character set substituted for each '?'/'*' position in --checksum-mask" placeholder:"CHARS" default:"abcdefghijklmnopqrstuvwxyz0123456789"`
	ChecksumLimit     int      `arg:"--checksum-limit" help:"maximum candidates generated per --checksum-mask/checksum before HTTP verification" placeholder:"N" default:"256"`
	ChecksumMaxLength int      `arg:"--checksum-max-length" help:"maximum characters a '*' wildcard in --checksum-mask expands to" placeholder:"N" default:"8"`
	BypassProbe       bool     `arg:"--bypass-probe" help:"unified read-only cookieless native-control bypass probe: give a managed endpoint (.aspx/.asmx/.ashx) to probe it, or a directory to scan+probe every endpoint found. Classifies the blinded native <location> control by baseline — 401 authentication (runs anonymously), 403 ipSecurity/require-SSL/app-pool, 404 requestFiltering. When the leading-token sweep finds nothing on a denied baseline, falls back to a segment-split probe (token fused inside the directory/extension the <location> keys on), which defeats FILE- and DIRECTORY-scoped controls the leading-token method alone misses. Managed <authorization> is NOT bypassed" default:"false"`
	ApppoolProbe      bool     `arg:"--apppool-probe" help:"compat alias of --bypass-probe (app-pool isolation is one of its classifications)" default:"false"`
	LocationProbe     bool     `arg:"--location-probe" help:"compat alias of --bypass-probe (<location> control bypass is one of its classifications)" default:"false"`
	DesyncProbe       bool     `arg:"--desync-probe" help:"raw-socket test for the HTTP request-smuggling preconditions: (http) does the back end forward a coexisting Content-Length + Transfer-Encoding and frame by TE (incl. obfuscated TE and bare-LF-hidden TE); (https) which RFC 9113-illegal HTTP/2 inputs http.sys accepts (h2->h1 downgrade preconditions, e.g. a space in :path). Read-only (smuggled request is GET /), with a pure-CL control so a non-vulnerable host is not misreported. Also runs automatically (quiet, once per host, silent unless a precondition is found) under --auto/--full" default:"false"`
	DirConfirm        []string `arg:"--dir-confirm,separate" help:"wildcard-free confirmation that a full 8.3 short name is a real DIRECTORY alias (repeatable; comma-lists ok). A direct GET (no '*'/'?') of a real directory alias routes into the managed pipeline (ASP.NET 404, no substatus) while a nonexistent name yields the native IIS 404.0 (substatus + Physical Path). Confirmation-only, directory-only; useful where a WAF strips the wildcard. Calibrates against a fake name first" placeholder:"SHORTNAME"`
	PathInfoProbe     []string `arg:"--pathinfo-probe,separate" help:"detect, black-box, whether a handler CONSUMES Request.PathInfo as a filesystem path (an arbitrary-file-read / CWE-22 CANDIDATE, an APPLICATION bug not an IIS bug). Give an extension-mapped handler URL (.aspx/.ashx/.asmx/.svc); it appends a benign PathInfo tail as a control, then a URL-legal but Windows-path-illegal char (|/\") — a 5xx differential means the handler maps PathInfo to a path (MapPath/File.*) — plus a reflection and physical-path-leak check. Flags a CANDIDATE only (verify by reading a known file); never exfiltrates. Also runs quietly under --auto/--full on resolved PathInfo-capable handler names, printing only a medium/high candidate (repeatable; comma-lists ok)" placeholder:"URL"`
	SourceProbe       bool     `arg:"--source-probe" help:"PT SWARM/DuoDrop source-code disclosure probe (CVE-2023-36899): give a reconstructed file URL under a protected .NET folder (e.g. https://host/bin/App.dll — get the 8.3 name from --index first) and it attempts the cookieless double-token split-join download (/(S(X))/b/(S(X))in/App.dll) that re-forms the hiddenSegment. Fires only where aggressive cookieless removal is active (unpatched, or RestoreAggressiveCookielessPathRemoval=true) with runAllManagedModulesForAllRequests=true for static targets" default:"false"`
	LootDir           string   `arg:"--loot-dir" help:"directory for saved source-disclosure loot (DLLs); files land in <dir>/<host>/<path>. Analyse them with 'shortloot'" placeholder:"DIR" default:"shortscan-loot"`
	Retrieve          bool     `arg:"--retrieve" help:"after confirming an 8.3 name, GET the alias through the selected origin and report/save it only when paired controls prove file bytes. Cross-stack retrieval is lab-confirmed for Go, Node serve-static, and MIME-mapped Kestrel StaticFiles aliases on Windows; nginx/Java remain stack-specific. Loot saved under --loot-dir" default:"false"`
	RetrieveBase      string   `arg:"--retrieve-base" help:"origin (scheme://host[:port]) to run --retrieve against, when the non-IIS retrieval front-end differs from the IIS host you enumerate on (shared NTFS root / reverse-proxy). Defaults to the target's origin" placeholder:"URL"`
	RetrieveStreams   []string `arg:"--retrieve-stream,separate" help:"with --retrieve, also read a known named NTFS alternate data stream through the selected retrieval origin (repeatable; give the stream name, e.g. Zone.Identifier). Each read uses a same-shape negative alias control and is saved separately" placeholder:"NAME"`
	WebDAV            bool     `arg:"--webdav" help:"when the target announces WebDAV (OPTIONS -> DAV header), PROPFIND Depth:1 each scanned directory to recover FULL long names (defeating the 6+3 short-name truncation) and flag requestFiltering-hidden child names (web.config, /bin, App_Data, *.bak/*.old/*.config) that a direct GET refuses. Recovers names, not blocked content; Depth:1 is one directory level" default:"false"`
	TildeContinuation bool     `arg:"--tilde-continuation" help:"recover the FULL long name of files whose name contains a literal ~<digit> (e.g. Backup~2024.zip, db~1.bak) by anchoring the oracle on the ~<digit> and enumerating past the 6+3 wall; also surfaces 8.3-legal ~<digit> files that have no short name and are otherwise invisible" default:"false"`
	Auto              bool     `arg:"--auto" help:"maximise per-item recovery: run every applicable technique in a cheap->expensive cascade, stopping at the first full-name success per item (wordlist, known-extensions, references, sibling, collision/checksum, webdav, tilde-continuation, then brute stem-completion at range 1-2) and, precondition-gated, retrieve (cross-stack, including Zone.Identifier, properties.dav, and guarded dir::$INDEX_ALLOCATION/child plus dir:$I30:$INDEX_ALLOCATION/child reads for recovered sensitive files when a non-IIS --retrieve-base is reachable) plus the source-probe disclosure chain for names recovered inside protected .NET folders (bypass/apppool/location probes stay opt-in). Add -i (or use --full) to also sweep the ASP.NET reserved folders (/bin, App_Code, App_Data, Views, Models, Controllers) through ::$INDEX_ALLOCATION — plain --auto no longer does. When the calibrated WebDAV capability oracle exists it profiles bounded current/recovered directories with $BITMAP and prioritises materialized-index recursion. Auto-enables the pieces whose precondition is met" default:"false"`
	Full              bool     `arg:"--full" help:"like --auto but exhaustive for reporting: run ALL techniques on every item even after a name is found (extra variants/siblings/extensions), and always brute (stem-completion at the deeper range 1-3); the reserved-folder ::$INDEX_ALLOCATION sweep covers the full set (adds App_GlobalResources, App_LocalResources, App_Browsers, App_WebReferences, App_Themes, Themes, Areas, App_Start, Migrations). Also enables --probe-candidates and --inspect-source (extra per-candidate/per-file requests). Heavier request volume; use on authorised targets without rate-limiting" default:"false"`
	Loop              bool     `arg:"--loop" help:"iteratively crawl -> scan -> recover -> re-crawl the RECOVERED files until a round finds nothing new (bounded, dedup'd — no infinite recursion); enables --crawl-references and deepens the reference loop. --auto already loops at depth CrawlMaxDepth+2; --loop raises the ceiling so deep reference chains (page A -> B -> C) are followed to the end" default:"false"`
	LoopMax           int      `arg:"--loop-max" help:"maximum rounds for --loop (0 = a high default)" placeholder:"N" default:"0"`
	CrawlReferences   bool     `arg:"--crawl-references" help:"build target-specific long-name candidates from bounded same-origin HTML/JS/CSS references" default:"false"`
	ReferenceOnly     bool     `arg:"--reference-only" help:"skip wordlist loading and recover long names only from crawled references (implies --crawl-references)" default:"false"`
	CrawlSeeds        []string `arg:"--crawl-seed,separate" help:"relative or same-origin page/asset to seed --crawl-references (repeatable; target base is always included)" placeholder:"URL"`
	CrawlMaxPages     int      `arg:"--crawl-max-pages" help:"maximum referenced pages/assets fetched per origin" placeholder:"N" default:"24"`
	CrawlMaxDepth     int      `arg:"--crawl-max-depth" help:"maximum same-origin reference depth" placeholder:"N" default:"2"`
	CrawlBodyLimit    int      `arg:"--crawl-body-limit" help:"maximum bytes read from each crawled page/asset" placeholder:"BYTES" default:"262144"`
	MutateExt         bool     `arg:"--mutate-ext" help:"after a hit, also probe common backup/source extensions (.bak,.old,.txt,~,etc)" default:"false"`
	InspectSource     bool     `arg:"--inspect-source" help:"after each confirmed file, fetch and sniff body for source/binary disclosure (extra requests; can be heavy)" default:"false"`
	KnownExtensions   bool     `arg:"--known-extensions" help:"also pair matching filename stems with well-known full extensions (for example ASP -> ASPX)" default:"false"`
	Brute             bool     `arg:"--brute" help:"last-resort recovery for a classic (non-checksummed) short name whose real length exceeds the 6-char 8.3 boundary: the tilde-oracle can only ever prove the observed 6 stem chars + 3 extension chars, nothing past that is queryable, so this proposes candidates instead and HTTP-verifies them through the configured --autocomplete oracle. Tries every real extension that 8.3-truncates to the observed short extension (ASP -> .asp/.aspx) paired with every --brute-charset completion of the stem, shortest first, stopping at the first confirmed match. Opt-in — expensive; included by --auto (range 1-2) and --full (range 1-3)" default:"false"`
	BruteRange        string   `arg:"--brute-range" help:"how many extra characters to append to the known 6-char stem, as a MIN-MAX (or MIN,MAX) range — e.g. 1-3 tries 1,2,3 extra chars; a bare N means 1-N. Each extra level multiplies request volume by the charset size. Default is mode-dependent when unset: 1-2 under --auto or a bare --brute, 1-3 under --full" placeholder:"RANGE" default:""`
	BruteCharset      string   `arg:"--brute-charset" help:"character set tried for each extra stem character" placeholder:"CHARS" default:"abcdefghijklmnopqrstuvwxyz0123456789"`
	BruteLimit        int      `arg:"--brute-limit" help:"maximum HTTP verification requests spent on --brute for the whole directory (shared across every unresolved short-name group in it, not per group — a directory with many unresolved names would otherwise multiply the request volume by however many it has)" placeholder:"N" default:"2000"`
	ProbeCandidates   bool     `arg:"--probe-candidates" help:"probe every long-name candidate once per collision group and report controlled hits" default:"false"`
	ProbeShorts       []string `arg:"--probe-short,separate" help:"select --probe-candidates/candidate-export collision groups by observed short name (repeatable; default is all)" placeholder:"SHORTNAME"`
	ProbeStatus       string   `arg:"--probe-status" help:"accepted hit statuses (comma-separated codes/ranges)" placeholder:"CODES" default:"200"`
	ProbeOracle       string   `arg:"--probe-oracle" help:"long-name verification oracle (status|distance|allow-copy|translate); allow-copy pins read-only PROPFIND Depth:0; translate pins GET + Translate:f (a server that ignores it may process GET normally). Both use paired controls and ignore probe-status/method/body-limit" placeholder:"MODE" default:"status"`
	ProbeMethod       string   `arg:"--probe-method" help:"read-only HTTP method for long-name verification (GET|HEAD|OPTIONS|TRACE|DEBUG|PROPFIND|_)" placeholder:"METHOD" default:"GET"`
	ProbeSuffix       string   `arg:"--probe-suffix" help:"raw suffix appended only to long-name verification and its controls" placeholder:"SUFFIX" default:""`
	ProbeBodyLimit    int      `arg:"--probe-body-limit" help:"maximum response bytes used by the distance oracle" placeholder:"BYTES" default:"4096"`
	CandidateOutput   string   `arg:"--candidate-output" help:"write generated candidate URLs, one per line, for tools such as httpx or ffuf" placeholder:"FILE"`
	OutputFile        string   `arg:"--output-file" help:"write results to FILE instead of stdout" placeholder:"FILE"`
	Quiet             bool     `arg:"--quiet,-q" help:"suppress banner and decorative headers" default:"false"`
	Output            string   `arg:"-o" help:"output format (human|json|ndjson|csv). csv carries only recovered/short-name result records — fingerprint, status, statistics, and other ad-hoc records are dropped from csv (available in json/ndjson)" placeholder:"format" default:"human"`
	Verbosity         int      `arg:"-v" help:"how much noise to make (0 = quiet; 1 = debug; 2 = trace)" default:"0"`
	FullUrl           bool     `arg:"--full-url,-F" help:"display the full URL for confirmed files rather than just the filename" default:"false"`
	Recurse           bool     `arg:"--recurse,-r" help:"descend into discovered subdirectories (forward recursion); disabled by default" default:"false"`
	Stabilise         bool     `arg:"-s" help:"attempt to get coherent autocomplete results from an unstable server (generates more requests)" default:"false"`
	Patience          int      `arg:"-p" help:"patience level when determining vulnerability (0 = patient; 1 = very patient)" placeholder:"LEVEL" default:"0"`
	Characters        string   `arg:"-C" help:"filename characters to enumerate" default:"JFKGOTMYVHSPCANDXLRWEBQUIZ8549176320-_()&'!#$%@^{}~"`
	Autocomplete      string   `arg:"-a" help:"autocomplete detection mode (auto = autoselect; method = HTTP method magic; status = HTTP status; distance = Levenshtein distance; allow-copy = WebDAV PROPFIND Depth:0 COPY-in-Allow existence differential, for hosts where GET-status is muddied; none = disable)" placeholder:"mode" default:"auto"`
	IsVuln            bool     `arg:"--is-vuln,-V" help:"bail after determining whether the service is vulnerable" default:"false"`
	Fingerprint       bool     `arg:"--fingerprint" help:"conservative per-host stack fingerprint beyond the Server header: parses IIS version/sc-substatus from detailed errors, classifies ::$INDEX_ALLOCATION and cookieless routing signals without claiming content read, identifies ambiguous mixed/non-IIS front ends, lists WebDAV methods as advertised-only, and confirms Allow/COPY only with paired controls. Read-only" default:"false"`
	Index             bool     `arg:"-i" help:"test ::$INDEX_ALLOCATION and :$i30:$INDEX_ALLOCATION on the given URL (standalone). Combined with --auto/--full it becomes a modifier that enables the reserved-folder (/bin, App_Code, App_Data, Views, Models, Controllers) ::$INDEX_ALLOCATION sweep during the scan"`
	BackwardsRecurse  bool     `arg:"--backwards-recurse,-R" help:"regressive scanning on parent directories (backwards/ascend); -r enables forward recursion" default:"false"`
	RelaxMatch        bool     `arg:"--relax,-X" help:"relax final negative match check and report tentative matches (Jakarta/CFM/SVC)" default:"false"`
}

func (arguments) Version() string {
	return getBanner()
}

var args arguments

// getBanner returns the main banner
func getBanner() string {
	art := `
  __ _                _   TheZakMan & bitquark
 / _\ |__   ___  _ __| |_ ___  ___ __ _ _ __
 \ \| '_ \ / _ \| '__| __/ __|/ __/ _` + "`" + ` | '_ \
 _\ \ | | | (_) | |  | |_\__ \ (_| (_| | | | |
 \__/_| |_|\___/|_|   \__|___/\___\__,_|_| |_|`
	return color.New(color.FgCyan, color.Bold).Sprint(art) + "\n\n" +
		color.New(color.FgBlue, color.Bold).Sprint(" an IIS short filename enumeration 🧩 v"+version)
}

// pathEscape returns an escaped URL with spaces encoded as %20 rather than + (which can cause odd behaviour from IIS in some modes)
func pathEscape(url string) string {
	return strings.Replace(nurl.QueryEscape(url), "+", "%20", -1)
}

// formatBytes renders a byte count the way the rest of the compact section
// summaries do — short, human-scaled, no decimals below 1 KB so "216 B" and
// "5.1 KB" read at a glance instead of a raw byte count.
func formatBytes(n int) string {
	switch {
	case n >= 1<<20:
		return fmt.Sprintf("%.1f MB", float64(n)/(1<<20))
	case n >= 1<<10:
		return fmt.Sprintf("%.1f KB", float64(n)/(1<<10))
	default:
		return fmt.Sprintf("%d B", n)
	}
}

// pluralCount renders "1 page" / "4 pages" — used throughout the compact
// section-summary lines ([REF-CRAWL], [WEBDAV-LIFT], …).
func pluralCount(n int, singular, plural string) string {
	word := plural
	if n == 1 {
		word = singular
	}
	return fmt.Sprintf("%d %s", n, word)
}

// isDotSegment reports whether name is "." or ".." — the two values that turn
// a recovered/reported filename into path navigation instead of a literal path
// segment once it's concatenated into a URL (recovery.go's foundDirectories,
// webdav.go's PROPFIND lift, wordlist.go, collision.go). Every recovery path
// that can end up feeding an external string into that concatenation must
// reject these first, same guard class as references.go and aliasprobe.go
// already apply to untrusted path segments.
func isDotSegment(name string) bool {
	return name == "." || name == ".."
}

// tildify takes a tilde-bearing fragment ("~1", "*~", etc.) and rewrites
// every '~' according to --tilde-encoding. Used to bypass WAFs that fingerprint the literal char.
func tildify(s string) string {
	if args.TildeEncoding == "" || args.TildeEncoding == "default" {
		return s
	}
	return strings.ReplaceAll(s, "~", encodeTilde())
}

// encodeTilde returns the encoded form of '~' according to --tilde-encoding.
// Modes: default (literal ~), percent (%7E), unicode (full-width U+FF5E),
// double (%257E), iis-unicode (%u007e), all (rotate).
func encodeTilde() string {
	mode := strings.ToLower(args.TildeEncoding)
	if mode == "all" {
		modes := []string{"default", "percent", "unicode", "double", "iis-unicode"}
		mode = modes[rand.Intn(len(modes))]
	}
	switch mode {
	case "percent":
		return "%7E"
	case "unicode":
		return "%EF%BD%9E"
	case "double":
		return "%257E"
	case "iis-unicode":
		return "%u007e"
	default:
		return "~"
	}
}

// expandUrlArgs resolves any "@file" entries in the positional URL list to their contents
func expandUrlArgs(in []string) []string {
	var out []string
	for _, u := range in {
		if strings.HasPrefix(u, "@") {
			fn := u[1:]
			fh, err := os.Open(fn)
			if err != nil {
				log.WithFields(log.Fields{"file": fn, "err": err}).Fatal("Unable to open URL file (@-prefix)")
			}
			urls, err := readURLList(fh)
			fh.Close()
			if err != nil {
				log.WithFields(log.Fields{"file": fn, "err": err}).Fatal("Unable to read URL file (@-prefix)")
			}
			out = append(out, urls...)
		} else {
			out = append(out, u)
		}
	}
	return out
}

// Run kicks off scans from the command line
// motwStream is the Mark-of-the-Web NTFS alternate data stream that Windows writes
// onto files downloaded through a browser or email client. It is a single, well-known
// name (never enumeration), so --auto can read it opportunistically through the
// cross-stack retrieval path.
const motwStream = "Zone.Identifier"

// applyAutoCascade turns the --auto/--full switch into the concrete set of recovery
// techniques it implies. It is extracted from Run so the mode's expansion is a pure,
// unit-testable transform on the arguments struct. Operator-supplied values are never
// overridden (see the RetrieveStreams guard).
func applyAutoCascade(a *arguments) {
	if !(a.Auto || a.Full) {
		return
	}
	a.KnownExtensions = true
	a.SiblingRecovery = true
	a.CollisionAncestry = true
	a.CrawlReferences = true
	a.WebDAV = true
	a.TildeContinuation = true
	a.MutateExt = true
	a.Retrieve = true
	a.Fingerprint = true
	// Stem completion is a last-resort recovery (only spends its budget on aliases
	// every cheaper technique already failed to resolve), so it is cheap enough for
	// --auto; its depth is the mode-dependent --brute-range resolved above (1-2 for
	// --auto, 1-3 for --full).
	a.Brute = true
	// Cross-stack retrieval chain: --retrieve is on, so when a non-IIS retrieval tier
	// is actually reachable (via --retrieve-base, or a mixed-stack origin) and the
	// operator named no explicit ADS, opportunistically read the near-ubiquitous
	// Zone.Identifier (Mark-of-the-Web) stream. It is a known name (never enumeration),
	// carries its own same-shape negative-alias control, is saved separately, and
	// reports only on proven bytes. It costs one cheap probe per served alias and is
	// silent on the single-stack-IIS skip, where retrieval does not run at all.
	if a.Retrieve && len(a.RetrieveStreams) == 0 {
		a.RetrieveStreams = []string{motwStream}
	}
	if a.Full {
		a.ProbeCandidates = true
		a.InspectSource = true
	}
}

func Run() {
	rand.Seed(time.Now().UTC().UnixNano())
	p := arg.MustParse(&args)
	args.Autocomplete = strings.ToLower(args.Autocomplete)
	if args.Autocomplete != "auto" && args.Autocomplete != "method" && args.Autocomplete != "status" && args.Autocomplete != "distance" && args.Autocomplete != "allow-copy" && args.Autocomplete != "none" {
		p.Fail("autocomplete must be one of: auto, status, method, distance, allow-copy, none")
	}
	args.ProbeOracle = strings.ToLower(args.ProbeOracle)
	switch args.ProbeOracle {
	case "status", "distance", "allow-copy", "translate":
	default:
		p.Fail("probe-oracle must be one of: status, distance, allow-copy, translate")
	}
	args.ProbeMethod = strings.ToUpper(strings.TrimSpace(args.ProbeMethod))
	if _, err := http.NewRequest(args.ProbeMethod, "https://example.invalid/", nil); err != nil {
		p.Fail("invalid probe-method: " + err.Error())
	}
	switch args.ProbeMethod {
	case "GET", "HEAD", "OPTIONS", "TRACE", "DEBUG", "PROPFIND", "_":
	default:
		p.Fail("probe-method must be read-only: GET, HEAD, OPTIONS, TRACE, DEBUG, PROPFIND, or _")
	}
	if args.ProbeOracle == "distance" && args.ProbeMethod == "HEAD" {
		p.Fail("probe-oracle distance cannot be used with HEAD because HEAD has no response body")
	}
	if args.ProbeBodyLimit < 1 || args.ProbeBodyLimit > 1024*1024 {
		p.Fail("probe-body-limit must be between 1 and 1048576 bytes")
	}
	args.Output = strings.ToLower(args.Output)
	switch args.Output {
	case "human", "json", "ndjson", "csv":
	default:
		p.Fail("output must be one of: human, json, ndjson, csv")
	}
	if len(args.RetrieveStreams) > 0 && !(args.Retrieve || args.Auto || args.Full) {
		p.Fail("retrieve-stream requires --retrieve, --auto, or --full")
	}
	if len(args.RetrieveStreams) > 0 {
		seen := make(map[string]struct{}, len(args.RetrieveStreams))
		normalized := make([]string, 0, len(args.RetrieveStreams))
		for _, raw := range args.RetrieveStreams {
			stream, err := normalizeRetrieveStream(raw)
			if err != nil {
				p.Fail("retrieve-stream: " + err.Error())
			}
			key := strings.ToLower(stream)
			if _, ok := seen[key]; ok {
				continue
			}
			seen[key] = struct{}{}
			normalized = append(normalized, stream)
		}
		args.RetrieveStreams = normalized
	}
	args.TildeEncoding = strings.ToLower(args.TildeEncoding)
	switch args.TildeEncoding {
	case "default", "percent", "unicode", "double", "iis-unicode", "all":
	default:
		p.Fail("tilde-encoding must be one of: default, percent, unicode, double, iis-unicode, all")
	}
	args.SessionStyle = strings.ToLower(args.SessionStyle)
	switch args.SessionStyle {
	case "d", "x", "f", "a", "empty", "rand":
	default:
		p.Fail("session-style must be one of: d, x, f, a, empty, rand")
	}
	args.SessionEncoding = strings.ToLower(args.SessionEncoding)
	switch args.SessionEncoding {
	case "literal", "outer", "asymmetric", "asymmetric-full":
	default:
		p.Fail("session-encoding must be one of: literal, outer, asymmetric, asymmetric-full")
	}
	args.ExactProfile = strings.ToLower(args.ExactProfile)
	switch args.ExactProfile {
	case "auto", "direct", "late", "late-encoded":
	default:
		p.Fail("exact-short-profile must be one of: auto, direct, late, late-encoded")
	}
	args.ExactMethod = strings.ToUpper(args.ExactMethod)
	switch args.ExactMethod {
	case "AUTO", "HEAD", "OPTIONS", "TRACE":
	default:
		p.Fail("exact-short-method must be one of: auto, HEAD, OPTIONS, TRACE")
	}
	if args.ExactRepeats < 1 || args.ExactRepeats > 5 {
		p.Fail("exact-short-repeats must be between 1 and 5")
	}
	for _, shortName := range args.ExactShorts {
		alias, err := parseExactShortAlias(shortName)
		if err != nil {
			p.Fail("exact-short: " + err.Error())
		}
		if !alias.Automatic && args.ExactProfile != "auto" && args.ExactProfile != "direct" {
			p.Fail("exact-short-profile: custom 8.3 candidates support only auto or direct")
		}
	}
	if _, err := normalizeExactAliasAppRoot(args.ExactAppRoot); err != nil {
		p.Fail("exact-short-app-root: " + err.Error())
	}
	// Every one of these dispatches unconditionally (regardless of --auto/--full/-r)
	// to its own standalone mode and returns from Run() without ever reaching the
	// others — see the "if <flag> { ...; return }" chain below. Without this check,
	// combining two of them (e.g. --exact-short with --bypass-probe, or --dir-confirm
	// with --pathinfo-probe) silently ran only whichever was checked first and
	// dropped every other explicitly-requested flag with no error or warning.
	// --custom-sfn is deliberately excluded: unlike these, it is dual-mode by design
	// (standalone only when --auto/--full/-r are all unset; otherwise a per-directory
	// modifier that legitimately combines with a scan), so it doesn't belong in a
	// blanket "always standalone" exclusivity list.
	standaloneModes := map[string]bool{
		"exact-short":    len(args.ExactShorts) > 0,
		"index":          args.Index,
		"bitmap-profile": args.BitmapProfile,
		"bypass-probe":   args.BypassProbe || args.ApppoolProbe || args.LocationProbe,
		"source-probe":   args.SourceProbe,
		"desync-probe":   args.DesyncProbe,
		"dir-confirm":    len(args.DirConfirm) > 0,
		"pathinfo-probe": len(args.PathInfoProbe) > 0,
	}
	var active []string
	for name, set := range standaloneModes {
		if set {
			active = append(active, name)
		}
	}
	if len(active) > 1 {
		sort.Strings(active)
		p.Fail(fmt.Sprintf("%s are standalone modes and cannot be combined", strings.Join(active, ", ")))
	}
	if len(args.CrawlSeeds) > 0 || args.ReferenceOnly {
		args.CrawlReferences = true
	}
	if args.CrawlMaxPages < 1 || args.CrawlMaxPages > 512 {
		p.Fail("crawl-max-pages must be between 1 and 512")
	}
	if args.CrawlMaxDepth < 0 || args.CrawlMaxDepth > 8 {
		p.Fail("crawl-max-depth must be between 0 and 8")
	}
	if args.CrawlBodyLimit < 1024 || args.CrawlBodyLimit > 1024*1024 {
		p.Fail("crawl-body-limit must be between 1024 and 1048576 bytes")
	}
	if len(args.ChecksumMasks) > 0 {
		if args.ChecksumAlphabet == "" {
			p.Fail("checksum-alphabet must not be empty when --checksum-mask is used")
		}
		if args.ChecksumLimit < 1 || args.ChecksumLimit > 65536 {
			p.Fail("checksum-limit must be between 1 and 65536")
		}
		if args.ChecksumMaxLength < 1 || args.ChecksumMaxLength > 24 {
			p.Fail("checksum-max-length must be between 1 and 24")
		}
		for _, mask := range args.ChecksumMasks {
			stars := strings.Count(mask, "*")
			if stars == 0 && !strings.Contains(mask, "?") {
				p.Fail(fmt.Sprintf("checksum-mask %q must contain at least one '?' or '*' placeholder", mask))
			}
			if stars > 1 {
				p.Fail(fmt.Sprintf("checksum-mask %q may contain at most one '*' variable-length placeholder", mask))
			}
			// Budget the shortest concrete form; the runtime stops expanding a '*'
			// once a longer length would exceed the leaf budget.
			minMask := strings.Replace(mask, "*", "?", 1)
			forward, backward := hashrecover.EstimateLeaves(minMask, args.ChecksumAlphabet)
			if forward > hashrecover.DefaultMaxForwardLeaves || backward > hashrecover.DefaultMaxBackwardLeaves {
				p.Fail(fmt.Sprintf("checksum-mask %q is too large for the chosen alphabet (~%d/%d leaves); narrow the mask or --checksum-alphabet", mask, forward, backward))
			}
		}
	}
	// Resolve the --brute-range default by mode when the user didn't set it:
	// --full digs one level deeper (1-3) than --auto or a bare --brute (1-2).
	// Done before validation so the resolved value is what gets range-checked.
	if args.BruteRange == "" {
		args.BruteRange = defaultBruteRange(args.Full)
	}
	// Validated unconditionally (not gated on --brute) because --auto/--full can
	// still turn Brute on after this point — an out-of-range value must be
	// rejected up front regardless of which flag will end up enabling it.
	if args.BruteCharset == "" {
		p.Fail("brute-charset must not be empty")
	}
	// Bound the charset: with hi=4 the intermediate prefix set is charset^3, so an
	// unbounded charset (e.g. all 95 printables) OOMs before a single probe. 64 is
	// well above the ~52 characters an 8.3 short name can actually contain.
	if n := len([]rune(args.BruteCharset)); n > 64 {
		p.Fail(fmt.Sprintf("brute-charset must be at most 64 characters (got %d)", n))
	}
	if lo, hi, err := parseBruteRange(args.BruteRange); err != nil {
		p.Fail("brute-range: " + err.Error())
	} else if lo < 1 || hi > 4 {
		p.Fail("brute-range must lie within 1-4 (each extra level multiplies request volume by the charset size)")
	}
	if args.BruteLimit < 1 || args.BruteLimit > 100000 {
		p.Fail("brute-limit must be between 1 and 100000")
	}
	switch args.TLSMin {
	case "1.0", "1.1", "1.2", "1.3":
	default:
		p.Fail("tls-min must be one of: 1.0, 1.1, 1.2, 1.3")
	}
	var statusErr error
	bruteStatuses, statusErr = parseStatusCodes(args.ProbeStatus)
	if statusErr != nil {
		p.Fail("probe-status: " + statusErr.Error())
	}
	if args.Concurrency < 1 {
		p.Fail("concurrency must be at least 1")
	}
	if args.Timeout < 1 {
		p.Fail("timeout must be at least 1 second")
	}
	if args.Parallel < 1 {
		p.Fail("parallel must be at least 1")
	}
	if args.MaxTime < 0 {
		p.Fail("maxtime cannot be negative")
	}
	if args.Retries < 0 {
		p.Fail("retries cannot be negative")
	}
	if args.Rate < 0 {
		p.Fail("rate cannot be negative")
	}
	if sameFilePath(args.OutputFile, args.CandidateOutput) {
		p.Fail("output-file and candidate-output must be different files")
	}
	inputFiles := append([]string{}, args.Wordlists...)
	if args.List != "" {
		inputFiles = append(inputFiles, args.List)
	}
	for _, urlArg := range args.Urls {
		if strings.HasPrefix(urlArg, "@") {
			inputFiles = append(inputFiles, strings.TrimPrefix(urlArg, "@"))
		}
	}
	for _, outputFile := range []string{args.OutputFile, args.CandidateOutput} {
		for _, inputFile := range inputFiles {
			if sameFilePath(outputFile, inputFile) {
				p.Fail(fmt.Sprintf("output file %q must not overwrite input file %q", outputFile, inputFile))
			}
		}
	}

	// Redirect output to a file if requested
	if args.OutputFile != "" {
		fh, err := os.Create(args.OutputFile)
		if err != nil {
			log.WithFields(log.Fields{"err": err, "file": args.OutputFile}).Fatal("Unable to open --output-file")
		}
		outputWriter = fh
		defer fh.Close()
	}
	if args.CandidateOutput != "" {
		fh, err := os.Create(args.CandidateOutput)
		if err != nil {
			log.WithFields(log.Fields{"err": err, "file": args.CandidateOutput}).Fatal("Unable to open --candidate-output")
		}
		candidateOutputWriter = fh
		candidateOutputSeen = make(map[string]struct{})
		defer fh.Close()
	}

	if !args.Quiet {
		printHuman(getBanner())
	}

	// Graceful SIGINT: drain in-memory per-host blocks before exiting. os.Exit does
	// not run defers, so relying on each scan goroutine's deferred flush loses every
	// still-active host in --parallel human mode.
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, os.Interrupt)
	go func() {
		<-sigCh
		fmt.Fprint(os.Stderr, "\033[?25h")
		fmt.Fprintln(os.Stderr, "\n[interrupted] flushing partial results...")
		flushAllHostSinks()
		if f, ok := outputWriter.(interface{ Sync() error }); ok {
			_ = f.Sync()
		}
		if f, ok := candidateOutputWriter.(interface{ Sync() error }); ok {
			_ = f.Sync()
		}
		os.Exit(130)
	}()

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

	// Build HTTP client (proxy, TLS, HTTP/2)
	hc := buildClient()

	// Initialize global rate limiter
	if args.Rate > 0 {
		requestDelay = time.Duration(float64(time.Second) / float64(args.Rate))
		log.WithFields(log.Fields{"delay": requestDelay, "rate": args.Rate}).Info("Rate limit enabled")
	}

	st := &httpStats{}
	// Live stderr status line (spinner + request rate + current dir). Inert unless
	// output is an interactive human TTY; stops on return.
	defer progress.start(st)()

	if args.List != "" {
		f, err := os.Open(args.List)
		if err != nil {
			log.WithFields(log.Fields{"err": err}).Fatal("Unable to open URL list file")
		}
		urls, err := readURLList(f)
		f.Close()
		if err != nil {
			log.WithFields(log.Fields{"err": err}).Fatal("Error reading URL list file")
		}
		args.Urls = append(args.Urls, urls...)
	}

	// --auto / --full: one switch that turns on the whole recovery cascade so each
	// item gets the maximum chance of a full-name (and, precondition-gated, content)
	// recovery. --auto is balanced; --full is exhaustive for reporting.
	applyAutoCascade(&args)

	// --loop deepens the reference-following loop and enables the crawl even without --auto.
	if args.Loop {
		args.CrawlReferences = true
	}

	// Expand any @file entries from the positional URL list
	args.Urls = expandUrlArgs(args.Urls)
	// When no URLs are given on the command line and stdin is piped (not a TTY), read
	// newline-delimited URLs from it: `cat urls.txt | shortscan`, `echo url | shortscan`.
	if len(args.Urls) == 0 && !isatty.IsTerminal(os.Stdin.Fd()) && !isatty.IsCygwinTerminal(os.Stdin.Fd()) {
		urls, err := readURLList(os.Stdin)
		if err != nil {
			p.Fail("unable to read URLs from stdin: " + err.Error())
		}
		args.Urls = append(args.Urls, urls...)
	}
	if len(args.ExactShorts) > 0 {
		if len(args.Urls) == 0 {
			p.Fail("exact-short requires at least one URL")
		}
		runExactShortProbes(args.Urls, hc, st)
		return
	}
	if len(args.CustomSFN) > 0 {
		if len(args.Urls) == 0 {
			p.Fail("custom-sfn requires at least one base URL to resolve the alias against")
		}
		// Standalone fast read when no scan is requested; with --auto/--full/-r the
		// aliases are instead probed at every scanned directory during the run.
		if !args.Auto && !args.Full && !args.Recurse {
			runCustomSFNProbes(args.Urls, hc, st)
			printFinishedStats(st)
			return
		}
	}
	if args.BitmapProfile {
		if len(args.Urls) == 0 {
			p.Fail("bitmap-profile requires at least one non-root directory URL")
		}
		runBitmapProfiles(args.Urls, hc, st)
		return
	}
	if args.BypassProbe || args.ApppoolProbe || args.LocationProbe {
		if len(args.Urls) == 0 {
			p.Fail("bypass-probe requires at least one URL: a managed endpoint (e.g. https://host/secure/Panel.aspx) to probe directly, or a directory (e.g. https://host/) to scan and probe every endpoint found; --list FILE works too")
		}
		runBypassProbeMode(args.Urls, hc, st)
		printFinishedStats(st)
		return
	}
	if args.SourceProbe {
		if len(args.Urls) == 0 {
			p.Fail("source-probe requires at least one file URL under a protected .NET folder, e.g. https://host/bin/App_Web_xxxx.dll (reconstruct the name from a prior `shortscan --index https://host/bin/` run); --list FILE works too")
		}
		runSourceProbeMode(args.Urls, hc, st)
		printFinishedStats(st)
		return
	}
	if args.DesyncProbe {
		if len(args.Urls) == 0 {
			p.Fail("desync-probe requires at least one origin URL (e.g. http://host/) to raw-socket-test for the TE.CL request-smuggling precondition")
		}
		runDesyncProbe(args.Urls, hc, st)
		printFinishedStats(st)
		return
	}
	if len(args.DirConfirm) > 0 {
		if len(args.Urls) == 0 {
			p.Fail("dir-confirm requires at least one base URL (e.g. http://host/) to resolve the candidate directory 8.3 aliases against")
		}
		runDirConfirm(args.Urls, args.DirConfirm, hc, st)
		printFinishedStats(st)
		return
	}
	if len(args.PathInfoProbe) > 0 {
		runPathInfoProbe(args.PathInfoProbe, hc, st)
		printFinishedStats(st)
		return
	}
	if len(args.Urls) == 0 {
		p.Fail("no target URLs supplied; provide a URL, --list FILE, @FILE, or URLs on stdin")
	}
	mk := markers{}
	wc, err := configureWordlists(args.Wordlists)
	if err != nil {
		log.WithFields(log.Fields{"err": err}).Fatal("Unable to configure wordlist")
	}
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	translateBaselines = make(map[string]translateBaseline)
	fingerprintMutex.Lock()
	fingerprintDone = make(map[string]bool)
	fingerprintMutex.Unlock()
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	vulnerableCount = 0

	// -i on its own is a standalone probe of the given URL's ADS forms. Combined with
	// --auto/--full it is instead a modifier: fall through to the scan, where the
	// reserved-folder ::$INDEX_ALLOCATION sweep (indexChainURLs) is now gated on it.
	if args.Index && !args.Auto && !args.Full && len(args.Urls) > 0 {
		testIndexAllocations(args.Urls, hc, st, wc, mk)
		return
	}

	// -i (or --full) combined with --auto/--full: if the user pointed a top-level
	// target directly at a reserved ASP.NET folder (…/bin, …/App_Code, …), redirect
	// it to the ::$INDEX_ALLOCATION form up front. Without this, the bare directory
	// URL got scanned as its own target first — a guaranteed-negative "8.3 oracle:
	// no" / "Vulnerable: No" (a plain directory has no differential oracle) — and
	// only the LATER, separately-queued ADS-suffixed form (discovered mid-scan via
	// indexChainURLs) carried the real one, so one target produced two contradictory
	// fingerprint blocks. See redirectReservedFolderURL's doc comment.
	for i, u := range args.Urls {
		args.Urls[i] = redirectReservedFolderURL(u)
	}

	// Scan each top-level URL independently: its own visited map, its own recovery
	// knowledge (siblingStems/references are per-Scan), and its own per-URL --maxtime
	// deadline. --parallel > 1 runs them concurrently for EVERY output mode: the shared
	// global caches (status/distance/allow-copy/translate/fingerprint/single-stack) are
	// all mutex-guarded and output lines are serialised (outputMu / progress.write), so
	// human blocks interleave line-atomically rather than corrupting. Set --parallel 1
	// to keep one host's block contiguous.
	parallel := args.Parallel
	multiHost := parallel > 1 && len(args.Urls) > 1
	// Human output from concurrent hosts is buffered per-host and flushed as one
	// labelled block on completion (see output.go) so blocks never interleave
	// line-by-line; the status bar meanwhile shows aggregate host completion
	// instead of per-directory churn. json/ndjson stream unbuffered (self-tagged).
	bufferHuman := multiHost && args.Output == "human"
	if multiHost {
		progress.setParallel(len(args.Urls))
	}
	if bufferHuman {
		enableHostSinks()
	}
	sem := make(chan struct{}, parallel)
	var wg sync.WaitGroup
	for _, u := range args.Urls {
		sem <- struct{}{}
		wg.Add(1)
		go func(u string) {
			defer wg.Done()
			defer func() { <-sem }()
			defer progress.incHostDone()
			if bufferHuman {
				beginHostSink(u)
				defer flushHostSink()
			}
			// Per-host resilience: one malformed/hostile target must never take down a
			// whole bulk run. Recover, log the panic + stack (so it can still be
			// reported), and let the other hosts finish. Registered last so it runs
			// first on unwind, ahead of the flush/counter/semaphore defers above.
			defer func() {
				if r := recover(); r != nil {
					log.WithFields(log.Fields{"url": u, "panic": r, "stack": string(debug.Stack())}).Error("scan panicked; skipping this host")
				}
			}()
			Scan([]string{u}, hc, st, wc, mk, make(map[string]struct{}))
		}(u)
	}
	wg.Wait()
	printFinishedStats(st)
}
