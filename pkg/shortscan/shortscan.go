package shortscan

import (
	"fmt"
	"math/rand"
	"net/http"
	nurl "net/url"
	"path"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
)

// base types, stats and wordlist records

type baseRequest struct {
	url   string
	file  string
	tilde string
	ext   string
}

type markers struct {
	statusPos    int
	statusNeg    int
	headerOracle bool
	headerPos    responseHeaderClass
	headerNeg    responseHeaderClass
}

type attackConfig struct {
	// autocomplete is this host's resolved long-name recovery oracle mode
	// ("method"/"status"/"distance"/"allow-copy"/"none"). It is resolved once
	// per host from args.Autocomplete (which stays "auto" until then) and
	// stored here rather than written back to the global args field: args is
	// shared package state, and --parallel runs one goroutine per host, so
	// writing the resolved mode into args.Autocomplete raced between hosts
	// (one host's "method" could be read by another host mid-resolution as
	// "status", silently corrupting its recovery decisions). Every downstream
	// read of the resolved mode goes through this field instead.
	autocomplete      string
	detectionOracle   string
	method            string
	suffix            string
	tildes            []string
	oracleProfiles    []oracleProfile
	fileChars         map[string]string
	extChars          map[string]string
	markersByTilde    map[string]markers
	aliasClaims       map[string]struct{}
	foundFiles        map[string]struct{}
	foundDirectories  map[string]struct{}
	bruteGroups       map[string]struct{}
	observedAliases   map[string]baseRequest
	siblingStems      *siblingStemKnowledge
	references        *referenceKnowledge
	referenceSeeds    map[string]struct{}
	wordlist          *wordlistConfig
	distanceMutex     sync.Mutex
	autocompleteMutex sync.Mutex
	referenceMutex    sync.Mutex
	// enumEntries buffers each confirmed/tentative short-name result (structured)
	// instead of printing it inline from the enumerate() goroutine that found it.
	// enumerate() is concurrent, so printing inline produced a different line
	// order every run; Scan() sorts by the plain 8.3 short name and prints after
	// wg.Wait() so the order is deterministic, collapsing the ordinal-agnostic
	// duplicates a collision group emits (see enumEntry.dedupKey).
	enumMutex   sync.Mutex
	enumEntries []enumEntry
	// deferredFindings buffers side-findings (retrieve / mutation / disclosure /
	// brute) emitted from the concurrent enumerate() worker goroutines, which cannot
	// reach the per-host --parallel output sink (it is keyed to the main scan
	// goroutine). Scan() flushes them on the main goroutine after wg.Wait() so they
	// land in the right host's block. Guarded by enumMutex. See emitHuman.
	deferredFindings []string
	// confirmedAliases records each confirmed 8.3 alias when --webdav is set, so the
	// per-directory runWebDAVLift can tie PROPFIND-recovered long names back to them.
	// Per-scan (not a package global) so a --parallel run never mixes one host's
	// aliases into another's lift. Guarded by enumMutex (appended from workers).
	confirmedAliases []confirmedAlias
	// sourceHits collects source-disclosure candidates found during enumeration. It
	// is a pointer to a per-scan store shared across this scan's directories, drained
	// by runSourceAutoChain after the loop — per-scan so --parallel never reports one
	// host's disclosure under another.
	sourceHits *sourceHitStore
	// pathInfoHits collects CONFIRMED PathInfo file reads (--auto/--full) for the
	// prominent end-of-scan summary; per-scan, threaded like sourceHits.
	pathInfoHits *pathInfoHitStore
	// sectionStarted tracks whether a technique section ([REF-CRAWL],
	// [SHORTNAMES], [WEBDAV-LIFT], …) has already printed for the directory
	// currently being scanned — see beginSection.
	sectionStarted bool
}

// emitHuman routes a side-finding line so it lands in the right place under
// --parallel. Those findings are produced inside enumerate()'s worker goroutines,
// whose output cannot reach the per-host bulk sink (keyed to the main scan
// goroutine), so in that mode they are buffered here and flushed by the main
// goroutine after enumeration (see flushDeferredFindings, called before the crawl/
// sibling/collision phases). Everywhere else — single host or JSON — they print
// inline. NOTE: the post-enumeration recovery phases (reference/sibling/collision)
// each run their OWN worker pool and must NOT use emitHuman: flushDeferredFindings
// has already fired by then, so a buffered line would never flush. They instead
// collect into a local slice and print it after their wg.Wait() on the calling
// (main) goroutine, which is where the sink lives. Variadic so a multi-line finding
// is buffered atomically (kept together).
func (ac *attackConfig) emitHuman(lines ...string) {
	if bulkCompact() && currentSink() == nil {
		ac.enumMutex.Lock()
		ac.deferredFindings = append(ac.deferredFindings, lines...)
		ac.enumMutex.Unlock()
		return
	}
	for _, l := range lines {
		printHuman(l)
	}
}

// flushDeferredFindings prints the buffered worker findings on the calling
// (main) goroutine, where printHuman reaches the per-host sink. Call after the
// enumerate wg.Wait(), when no worker can still be appending.
func (ac *attackConfig) flushDeferredFindings() {
	ac.enumMutex.Lock()
	lines := ac.deferredFindings
	ac.deferredFindings = nil
	ac.enumMutex.Unlock()
	for _, l := range lines {
		printHuman(l)
	}
}

// Version, rainbow table magic, default character set
const version = "1.81.1"
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
var pathSuffixes = [...]string{
	"/", "",
	"/.aspx", "?aspxerrorpath=/", "/.aspx?aspxerrorpath=/",
	"/.asmx", "/.vb",
	"/.cshtml", "/.vbhtml", "/.razor", "/.svc", "/.ashx",
	"/.config", "/a.aspx", "/b/.aspx",
}

// activeModes returns a compact list of the enabled non-default toggles and
// techniques for this run, so the header states plainly what the scan will do.
// resolvedToLongName reports whether a recovery match is a genuine HTTP-confirmed
// long-name resolution (green, shows a status, counts toward the X/Y-resolved
// tally) as opposed to a "short-name" alias echo (the recovered name still carries
// the ~<digit>) or a "wordlist-inferred" request-filtered guess — neither of which
// resolved the long name, so neither counts nor shows a (misleading) GET status.
func resolvedToLongName(fnr, matchType string) bool {
	return fnr != "" && !strings.HasPrefix(matchType, "short-name") && matchType != "wordlist-inferred"
}

// isTransientInfraStatus reports whether an HTTP status is an infrastructure
// "no answer" from a proxy/CDN/load balancer (rate limit or an unhealthy/absent
// backend) rather than a real resource-existence answer from IIS. The 8.3
// existence oracle keys on a status DIFFERENCE, so if these flap in and out —
// e.g. a Google Cloud LB / Cloud Armor front end fanning to backends whose
// health flaps, where the SAME probe returns 503, 404, 503, 503, 503, 404 —
// they manufacture a phantom positive (statusPos=503 != statusNeg=404) and the
// enumeration then explodes into hundreds of never-resolving false names. Such a
// status is never valid evidence of a short name's existence, so calibration
// must not accept it as a positive and enumeration must not count it as a hit.
//
// 500 is deliberately NOT here: a 500 can be a STABLE, legitimate existence
// signal (an IIS host answering the DEBUG verb 500 for a missing 8.3 and 404 for
// an existing one — a real, enumerable target seen live). A 500 that instead
// FLAPS (400,500,400,… on another live target's DEBUG verb) is rejected by the
// negative-baseline re-verification in probeOracleCombo, which distinguishes a
// stable oracle from a flapping one without blanket-banning the status.
func isTransientInfraStatus(code int) bool {
	switch code {
	case http.StatusTooManyRequests, // 429
		http.StatusBadGateway,         // 502
		http.StatusServiceUnavailable, // 503
		http.StatusGatewayTimeout:     // 504
		return true
	}
	return false
}

// negativeBaselineStable re-probes the "genuinely missing" negative shape a few
// more times and reports whether it STILL answers statusNeg every time. It is the
// guard that tells a stable oracle (one live target's DEBUG verb: neg=500 every
// time, pos=404 — real) apart from a flapping front end (another live target's
// DEBUG verb: neg bounces 400/500, so the 4-probe calibration can catch a 500
// burst and pair it against a 400 positive — phantom). Called only after a
// candidate positive is found, which is rare, so the extra probes cost little.
func negativeBaselineStable(hc *http.Client, st *httpStats, url, method, suffix string, statusNeg int) bool {
	for i := 0; i < 3; i++ {
		res, err := fetch(hc, st, method, fmt.Sprintf("%s*%d*%s", url, rand.Intn(5)+5, suffix))
		if err != nil || res.StatusCode != statusNeg {
			return false
		}
	}
	return true
}

func activeModes(autocomplete string) []string {
	var m []string
	add := func(s string) { m = append(m, s) }

	if args.Full {
		add(color.HiMagentaString("full"))
	} else if args.Auto {
		add(color.HiMagentaString("auto"))
	}

	// long-name recovery techniques
	if args.TildeContinuation {
		add("tilde-continuation")
	}
	// A wordlist is always in play unless --reference-only or -a none disables
	// candidate matching entirely — configureWordlists() falls back to the
	// embedded resources/wordlist.txt when -w isn't given, so say so instead of
	// silently omitting "wordlist" and implying no candidate matching ran.
	if !args.ReferenceOnly && needsConfiguredWordlist(autocomplete) {
		if len(args.Wordlists) > 0 {
			add("wordlist")
		} else {
			add("wordlist (default)")
		}
	}
	if args.KnownExtensions {
		add("known-extensions")
	}
	if args.SiblingRecovery {
		add("sibling-recovery")
	}
	if args.CollisionAncestry {
		add("collision-ancestry")
	}
	if len(args.ChecksumMasks) > 0 {
		add(fmt.Sprintf("checksum-mask×%d", len(args.ChecksumMasks)))
	}
	if args.ReferenceOnly {
		add("reference-only")
	} else if args.CrawlReferences {
		add("crawl-references")
	}
	if args.WebDAV {
		add("webdav")
	}
	if args.MutateExt {
		add("mutate-ext")
	}
	if args.ProbeCandidates {
		add("probe-candidates")
	}
	if args.Brute {
		add("brute " + args.BruteRange)
	}
	if args.InspectSource {
		add("inspect-source")
	}

	// probes / disclosure / exploitation
	if args.BypassProbe || args.ApppoolProbe || args.LocationProbe {
		add("bypass-probe")
	}
	if args.SourceProbe {
		add("source-probe")
	}
	if args.Index || args.Full {
		add("index-chain")
	}
	if args.Retrieve {
		add("retrieve")
	}
	if args.Fingerprint {
		add("fingerprint")
	}
	if len(args.CustomSFN) > 0 {
		add("custom-sfn")
	}

	// scan behaviour
	if args.Recurse {
		add("recurse")
	}
	if args.BackwardsRecurse {
		add("backwards-recurse")
	}
	if args.Stabilise {
		add("stabilise")
	}
	if args.RelaxMatch {
		add("relax")
	}

	// notable non-default settings
	// NOTE: the existence oracle (method/status) is intentionally NOT listed
	// here — see oracleNote(). It is re-resolved per directory (a reserved
	// folder commonly disagrees with its parent), so folding it into this
	// list would flip on nearly every block and defeat Running:/Active:'s dedup.
	if args.TildeEncoding != "" && args.TildeEncoding != "default" {
		add("tilde-enc=" + args.TildeEncoding)
	}
	if args.Rate > 0 {
		add(fmt.Sprintf("rate=%g/s", args.Rate))
	}
	return m
}

// webDAVDetectionVerbs are the verbs calibrateAltStatusOracle escalates to when
// the primary matrix (the common verbs) finds no 8.3 differential. Detection via
// one of these means the front end likely mutes the common verbs — which matters
// because long-name recovery still probes with the GET-based autocomplete oracle.
var webDAVDetectionVerbs = map[string]bool{
	"PROPFIND": true, "SEARCH": true, "PROPPATCH": true, "MKCOL": true, "LOCK": true,
}

func isWebDAVDetectionVerb(m string) bool { return webDAVDetectionVerbs[m] }

// oracleNote renders which existence oracle this directory resolved to, as a
// short suffix on the Vulnerable: line. Kept out of activeModes()/Active: on
// purpose — see the note above — since the oracle is re-resolved per
// directory and folding it into that list defeated its dedup.
func oracleNote(autocomplete, detMethod, detectionOracle string) string {
	if detectionOracle == "header-signature" {
		if autocomplete == "" || autocomplete == "none" {
			return color.HiBlackString("  (header signature via %s)", detMethod)
		}
		return color.HiBlackString("  (%s oracle · header signature via %s)", autocomplete, detMethod)
	}
	if autocomplete == "" || autocomplete == "none" {
		return ""
	}
	// Surface the detection verb when the 8.3 signal came from a WebDAV verb — on a
	// hardened target where the common verbs are muted, the operator wants to know an
	// uncommon verb (e.g. PROPPATCH) is what carried existence. autocomplete is the
	// long-name recovery oracle, a separate axis; both are worth showing here.
	if isWebDAVDetectionVerb(detMethod) {
		return color.HiBlackString("  (%s oracle · via %s)", autocomplete, detMethod)
	}
	return color.HiBlackString("  (%s oracle)", autocomplete)
}

// nonVulnerableLine renders a directory with no 8.3 files as a single dim
// line instead of a full header block. These make up the bulk of a --recurse
// run (the bin/App_Code/App_Data index-chain probes especially) and carry no
// finding worth a full block. The literal "Vulnerable: No" substring is kept
// so an existing `grep 'Vulnerable: No'` habit still works unchanged.
func nonVulnerableLine(url string, flagged bool) string {
	line := color.HiBlackString("  · %s — Vulnerable: No (or no 8.3 files exist)", url)
	if flagged {
		line += " " + color.HiRedString("[!]")
	}
	return line
}

// headerRule and sectionRule are two graduated-weight dividers, both the
// same width as the ════ endpoint rule. headerRule marks the one transition
// from a block's structured header (URL/Running/Active/Vulnerable) into its
// freeform body — always followed by a blank line, since that's the bigger
// conceptual jump. sectionRule marks the (tighter, no blank line) boundary
// between two things that both belong to that body: one technique section
// and the next, or a block's content and the compact "Vulnerable: No" lines
// for the directories queued right after it.
const (
	headerRule  = "________________________________________________________________________________"
	sectionRule = "--------------------------------------------------------------------------------"
)

// catchAllThreshold is the fraction of the character set that, once the 8.3
// oracle matches it as valid characters, marks a catch-all/soft-response server
// whose enumeration is all false positives. It sits well clear of any real
// directory (measured maxima: ~0.70 of the ~51-char set for first characters,
// ~0.55 for extension characters) while a true catch-all matches ~1.0. 0.9 is
// ~46 distinct characters — including symbols like ^ { } ~ that no real filename
// starts with — so a legitimate but diverse directory is not suppressed by mistake.
const catchAllThreshold = 0.9

// catchAllCharFraction returns the largest fraction of the character set the
// file-character oracle matched across the confirmed tildes. A value near 1.0 is
// the signature of a serve-everything front end (see the guard in Scan).
func catchAllCharFraction(fileChars map[string]string, tildes []string, charset string) float64 {
	n := len([]rune(charset))
	if n == 0 {
		return 0
	}
	max := 0.0
	for _, t := range tildes {
		if f := float64(len([]rune(fileChars[t]))) / float64(n); f > max {
			max = f
		}
	}
	return max
}

// discoverProfileChars measures one method/suffix profile in isolation. The
// maps are profile-local so characters observed through one handler can never
// be combined with a different handler later in the recursive walk.
func discoverProfileChars(hc *http.Client, st *httpStats, baseURL string, profile *oracleProfile) (fileFrac, extFrac float64) {
	profile.fileChars = make(map[string]string)
	profile.extChars = make(map[string]string)
	profile.dotExtChars = make(map[string]string)

	var charMu sync.Mutex
	fileHit := make(map[string]map[string]bool)
	extHit := make(map[string]map[string]bool)
	dotExtHit := make(map[string]map[string]bool)
	for _, tilde := range profile.tildes {
		fileHit[tilde] = make(map[string]bool)
		extHit[tilde] = make(map[string]bool)
		dotExtHit[tilde] = make(map[string]bool)
	}
	csem := make(chan struct{}, args.Concurrency)
	cwg := new(sync.WaitGroup)
	for shape := 0; shape < 3; shape++ {
		for _, char := range args.Characters {
			for _, tilde := range profile.tildes {
				cwg.Add(1)
				go func(shape int, char, tilde string) {
					csem <- struct{}{}
					defer func() { <-csem; cwg.Done() }()
					var candidate string
					switch shape {
					case 0:
						candidate = baseURL + "*" + pathEscape(char) + "*" + tilde + "*"
					case 1:
						candidate = baseURL + "*" + tilde + "*" + pathEscape(char) + "*"
					default:
						candidate = baseURL + "*" + tilde + "." + pathEscape(char) + "*"
					}
					res, err := profile.fetch(hc, st, candidate)
					if err != nil || !profile.matchesPositive(tilde, res) {
						return
					}
					charMu.Lock()
					switch shape {
					case 0:
						fileHit[tilde][char] = true
					case 1:
						extHit[tilde][char] = true
					default:
						dotExtHit[tilde][char] = true
					}
					charMu.Unlock()
				}(shape, string(char), tilde)
			}
		}
	}
	cwg.Wait()

	for _, tilde := range profile.tildes {
		var fb, eb, db strings.Builder
		for _, char := range args.Characters {
			c := string(char)
			if fileHit[tilde][c] {
				fb.WriteString(c)
			}
			if extHit[tilde][c] {
				eb.WriteString(c)
			}
			if dotExtHit[tilde][c] {
				db.WriteString(c)
			}
		}
		profile.fileChars[tilde] = fb.String()
		profile.extChars[tilde] = eb.String()
		profile.dotExtChars[tilde] = db.String()
	}
	fileFrac = catchAllCharFraction(profile.fileChars, profile.tildes, args.Characters)
	starExtFrac := catchAllCharFraction(profile.extChars, profile.tildes, args.Characters)
	dotExtFrac := catchAllCharFraction(profile.dotExtChars, profile.tildes, args.Characters)
	extFrac = starExtFrac
	if dotExtFrac > extFrac {
		extFrac = dotExtFrac
	}
	return fileFrac, extFrac
}

func rebuildMergedProfileChars(ac *attackConfig) {
	ac.fileChars = make(map[string]string)
	ac.extChars = make(map[string]string)
	ac.tildes = nil
	for i := range ac.oracleProfiles {
		profile := &ac.oracleProfiles[i]
		for _, tilde := range profile.tildes {
			ac.tildes = appendUniqueTilde(ac.tildes, tilde)
			for _, char := range args.Characters {
				if strings.ContainsRune(profile.fileChars[tilde], char) && !strings.ContainsRune(ac.fileChars[tilde], char) {
					ac.fileChars[tilde] += string(char)
				}
				if strings.ContainsRune(profile.extChars[tilde], char) && !strings.ContainsRune(ac.extChars[tilde], char) {
					ac.extChars[tilde] += string(char)
				}
			}
		}
	}
}

// beginSection prints sectionRule before a technique section's own first
// line, but only if another section has already printed since the last
// headerRule — the first section right after the header never needs one,
// since headerRule + the blank line already did that job.
func beginSection(ac *attackConfig) {
	if ac == nil || bulkCompact() {
		// Bulk-compact drops the inter-section rules entirely — the two-space
		// body indent is separation enough under the one-line host header.
		return
	}
	if ac.sectionStarted {
		printHuman(sectionRule)
	}
	ac.sectionStarted = true
}

// enumEntry is one buffered short-name result, kept structured so the print
// stage can sort deterministically, collapse the ordinal-agnostic duplicates a
// collision group emits, and count how many resolved to a full name.
type enumEntry struct {
	sortKey   string // plain 8.3 short name — the deterministic sort/display key
	dedupKey  string // group+"\x00"+fullname for unverified-ordinal recoveries; else ""
	line      string // fully rendered output line
	resolved  bool   // a full long name was recovered
	tentative bool   // --relax-only guess; must not suppress stronger recovery phases
}

// bufferEnum records a structured short-name result for deterministic, sorted,
// de-duplicated printing after enumerate()'s goroutines finish. A non-empty
// dedupKey marks the ordinal-agnostic recoveries a collision group produces
// (every ordinal resolves to the same full name); the print stage keeps the
// first and annotates it with the group size.
func bufferEnum(ac *attackConfig, sortKey, dedupKey, line string, resolved bool) {
	ac.enumMutex.Lock()
	ac.enumEntries = append(ac.enumEntries, enumEntry{sortKey: sortKey, dedupKey: dedupKey, line: line, resolved: resolved})
	ac.enumMutex.Unlock()
}

func bufferTentativeEnum(ac *attackConfig, sortKey, line string) {
	ac.enumMutex.Lock()
	ac.enumEntries = append(ac.enumEntries, enumEntry{sortKey: sortKey, line: line, tentative: true})
	ac.enumMutex.Unlock()
}

// claimDetectedAlias ensures that profiles can independently walk their own
// oracle trees without repeating recovery, output, retrieval or WebDAV effects
// for the same confirmed 8.3 alias. Profiles are enumerated in priority order,
// so the first claim is deterministic.
func claimDetectedAlias(ac *attackConfig, br baseRequest) bool {
	key := strings.ToLower(br.url + br.file + br.tilde + br.ext)
	ac.enumMutex.Lock()
	defer ac.enumMutex.Unlock()
	if ac.aliasClaims == nil {
		ac.aliasClaims = make(map[string]struct{})
	}
	if _, exists := ac.aliasClaims[key]; exists {
		return false
	}
	ac.aliasClaims[key] = struct{}{}
	return true
}

// bufferedShortNameSet returns the lowercased set of plain 8.3 short names the
// classic enumeration already buffered for this host. The tilde-continuation walk
// uses it to drop any recovered name that is really just one of those aliases — e.g.
// WEB~1.CON (web.config's generated short name, base < 6 so the fixed-6 degenerate
// guard never catches it) would otherwise be re-reported as a bogus "name past 6+3",
// exactly the redundant/misleading line the walk is meant to avoid.
func bufferedShortNameSet(ac *attackConfig) map[string]struct{} {
	if ac == nil {
		return nil
	}
	ac.enumMutex.Lock()
	defer ac.enumMutex.Unlock()
	set := make(map[string]struct{}, len(ac.enumEntries))
	for _, e := range ac.enumEntries {
		if e.tentative {
			continue
		}
		set[strings.ToLower(e.sortKey)] = struct{}{}
	}
	return set
}

// collapseEnumEntries sorts the buffered results by 8.3 short name, collapses the
// ordinal-agnostic duplicates a collision group emits (every ordinal ~1..~N
// resolves to the same full name with an unverified ordinal — keep the first,
// annotate it with the group size), and returns the render-ready lines plus how
// many resolved to a full name. Pure, so the collapse/count is unit-tested.
func collapseEnumEntries(entries []enumEntry) (lines []string, resolved int) {
	sort.Slice(entries, func(i, j int) bool { return entries[i].sortKey < entries[j].sortKey })
	memberCount := make(map[string]int)
	for _, e := range entries {
		if e.dedupKey != "" {
			memberCount[e.dedupKey]++
		}
	}
	seen := make(map[string]struct{})
	lines = make([]string, 0, len(entries))
	for _, e := range entries {
		if e.dedupKey != "" {
			if _, dup := seen[e.dedupKey]; dup {
				continue
			}
			seen[e.dedupKey] = struct{}{}
			if n := memberCount[e.dedupKey]; n > 1 {
				e.line += color.HiBlackString(" (1 of %d in group; ordinal unverified)", n)
			}
		}
		lines = append(lines, e.line)
		if e.resolved {
			resolved++
		}
	}
	return lines, resolved
}

func continueProfileEnumeration(sem chan struct{}, wg *sync.WaitGroup, hc *http.Client, st *httpStats, ac *attackConfig, profile *oracleProfile, br baseRequest, extMode bool) {
	if len(br.ext) == 0 {
		nr := br
		nr.ext = "."
		enumerate(sem, wg, hc, st, ac, profile, nr)
	}
	if !((extMode && len(br.ext) < 4) || (!extMode && len(br.file) < 6)) {
		return
	}
	var candidate string
	if extMode {
		candidate = br.url + pathEscape(br.file) + tildify(br.tilde) + pathEscape(br.ext) + "%3f*"
	} else {
		candidate = br.url + pathEscape(br.file) + "%3f*" + tildify(br.tilde) + "*" + pathEscape(br.ext)
	}
	res, err := profile.fetch(hc, st, candidate)
	if err == nil && profile.matchesNonNegative(br.tilde, res) {
		enumerate(sem, wg, hc, st, ac, profile, br)
	}
}

// enumerate builds and fetches candidate short name URLs using recursion
func enumerate(sem chan struct{}, wg *sync.WaitGroup, hc *http.Client, st *httpStats, ac *attackConfig, profile *oracleProfile, br baseRequest) {
	mk, ok := profile.markerForTilde(br.tilde)
	if !ok {
		return
	}

	// Determine if in extension enumeration mode
	extMode := len(br.ext) > 0

	// Select the character map to use
	var chars string
	if extMode {
		chars = profile.extChars[br.tilde]
	} else {
		chars = profile.fileChars[br.tilde]
	}

	// Loop through characters
	for _, char := range chars {
		wg.Add(1)
		go func(sem chan struct{}, wg *sync.WaitGroup, hc *http.Client, ac *attackConfig, profile *oracleProfile, mk markers, br baseRequest, char string) {
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
				url = br.url + pathEscape(br.file) + tildify(br.tilde) + pathEscape(br.ext) + "*"
			} else {
				br.file += char
				url = br.url + pathEscape(br.file) + "*" + tildify(br.tilde) + "*" + pathEscape(br.ext)
			}

			// Check if this looks like a hit
			res, err := profile.fetch(hc, st, url)
			if err == nil && profile.matchesPositive(br.tilde, res) {
				// Check if the full file part is reached
				res, err = profile.fetch(hc, st, br.url+pathEscape(br.file)+tildify(br.tilde)+"*"+pathEscape(br.ext))
				if err == nil && profile.matchesPositive(br.tilde, res) {
					detectionOracle, detectionMethod, detectionSuffix, detectionStatus := detectionEvidence(profile, res)
					res, err = profile.fetch(hc, st, br.url+pathEscape(br.file)+tildify(br.tilde)+pathEscape(br.ext))
					if err == nil && profile.matchesNonNegative(br.tilde, res) {
						if !claimDetectedAlias(ac, br) {
							continueProfileEnumeration(sem, wg, hc, st, ac, profile, br, extMode)
							return
						}
						match := recoverLongName(hc, st, ac, br)
						fnr := match.path
						detectionOracle, detectionMethod, detectionSuffix, detectionStatus = detectionEvidence(profile, res)
						resultBaseURL := br.url
						if match.baseURL != "" {
							resultBaseURL = match.baseURL
						}
						// --bypass-probe: collect each resolved full-name URL so the
						// probe can test the whole native-control family on it after the scan.
						if args.BypassProbe && fnr != "" {
							recordBypassTarget(resultBaseURL + strings.ToLower(fnr))
						}
						// --index auto-chain (PT SWARM/DuoDrop): a name recovered inside a
						// protected .NET folder (/bin, /App_Code, …) is a source-disclosure
						// candidate. If the .dll already verified 200 through the cookieless
						// split path (resultBaseURL then carries the token, e.g. …/b/(S(d))in/),
						// that URL IS the working disclosure; otherwise pass the clean folder
						// path to probeSourceURL to derive the payloads itself.
						// --retrieve: direct 8.3 alias retrieval — IIS blocks it (404.0),
						// but non-IIS / proxy static tiers serve the file (web.config, keys).
						if args.Retrieve {
							retrieveShortName(hc, st, ac, br)
						}
						// --webdav: remember each confirmed alias so the post-scan
						// PROPFIND name-lift can tie recovered long names back to it.
						if args.WebDAV {
							recordConfirmedAlias(ac, br)
						}
						if (args.Index || args.Auto || args.Full) && fnr != "" {
							if match.status == http.StatusOK && baseHasCookielessToken(resultBaseURL) {
								how := "canonical (recovered via --auto/--full index chain)"
								if args.Index {
									how = "canonical (recovered via -i)"
								}
								recordSourceHit(ac, sourceHit{workingURL: resultBaseURL + strings.ToLower(fnr), name: fnr, how: how})
							} else if isProtectedDotNetFolder(resultBaseURL) {
								// stripIndexAllocation truncates at "::$", dropping the trailing
								// slash, so re-normalise to exactly one "/" before the filename —
								// otherwise the probe URL becomes /binApp.dll and probeSourceURL
								// rejects it ("need a path like /bin/App.dll").
								probeURL := sourceProbeCandidate(resultBaseURL, fnr)
								recordSourceHit(ac, sourceHit{probeURL: probeURL, name: fnr})
							}
						}
						// A "short-name" match echoes the 8.3 alias back (its recovered name
						// still carries the ~<digit>); it confirms the alias exists but did
						// NOT resolve the long name. Treat it as UNRESOLVED so it neither
						// inflates the X/Y-resolved tally nor shows a GET status — that
						// status is only ever the alias probe (IIS's canonical-mismatch 404
						// or an auth 401), never the file, and reads as "resolved with 401".
						// A request-filtered name (web.config, *.config, global.asax) is
						// enumerable by its 8.3 alias but its long name is always hidden by IIS
						// (404.8/403), so the existence oracle can never confirm it — recovery
						// surfaces the matching wordlist entry as an INFERENCE, not a confirmed
						// resolution. Shown yellow + "?", never counted as resolved.
						isInferred := fnr != "" && match.matchType == "wordlist-inferred"
						resolvedLong := resolvedToLongName(fnr, match.matchType)
						sensitiveReason := sensitiveReasonForRecovered(fnr, match.matchType)
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
								switch {
								case resolvedLong && args.FullUrl:
									ff = color.GreenString(resultBaseURL) + color.HiGreenString(strings.ToLower(fnr))
								case resolvedLong:
									ff = color.HiGreenString(fnr)
								case isInferred:
									// strong wordlist guess for a request-filtered file; not HTTP-confirmed
									ff = color.YellowString(fnr + "?")
								default:
									// confirmed alias, long name unresolved: dim, no green, no status
									ff = color.HiBlackString(fnr)
								}
								// Show the confirmation status next to the name: on a real
								// target it tells the operator which recovered endpoints are
								// open (200), auth-walled (401/403) or redirecting (302).
								// Only for a real long-name resolution — never for the alias echo.
								if resolvedLong && match.status != 0 {
									ff += " (" + colorStatus(match.status) + ")"
								}
								if match.matchType != "" {
									ordinal := "ordinal unverified"
									if match.ordinalVerified {
										ordinal = "exact alias path"
									}
									ff += color.HiBlackString(" [%s; group %s; %s]", match.matchType, match.collisionGroup, ordinal)
									if match.checksum != "" {
										annotation := "ck=" + match.checksum
										if len(match.families) > 0 {
											annotation += "; families=" + strings.Join(match.families, ",")
										}
										if match.derivedFrom != "" {
											annotation += "; from " + match.derivedFrom
										}
										ff += color.HiBlackString(" [%s]", annotation)
									}
								}
								if sensitiveReason != "" {
									if isInferred {
										// Inferred from the wordlist, never HTTP-confirmed, and
										// request-filtered: IIS blocks a direct GET, so this grants
										// NO access. It must not read like a disclosure — no red
										// [SENSITIVE] tag, no "connection strings / machineKey" copy
										// that implies loot in hand. It is a candidate the operator
										// would still have to reach through some other vector.
										ff += "  " + color.YellowString("[candidate, not confirmed; request-filtered, no direct GET]")
									} else {
										ff += "  " + color.HiRedString("[SENSITIVE] %s", sensitiveReason)
									}
								}
							} else {
								if len(br.file) < 6 {
									fn = color.GreenString(fn)
								}
								if len(br.ext) < 4 {
									fe = color.GreenString(fe)
								}
								fp = strings.Replace(fn+fe, "?", color.HiBlackString("?"), -1)
								// Wholly unresolved (no wordlist/reference/sibling match at all)
								// AND extensionless — the exact shape a directory's own 8.3 alias
								// has (a file always carries SOME extension marker). Before now
								// the tool said nothing beyond the bare alias; --dir-confirm's
								// wildcard-free managed-vs-native 404 technique already existed
								// but only ran when the operator manually re-invoked it with an
								// already-suspected name. Auto-apply it here — it costs one extra
								// request (plus one calibration probe, once per origin, cached)
								// and silently adds nothing when the oracle isn't usable or the
								// name isn't confirmably a directory.
								if br.ext == "" && (args.Auto || args.Full) {
									if autoDirConfirmDirectory(hc, st, br.url, br.file+br.tilde) {
										fp += color.HiGreenString(" [DIR]")
									}
								}
							}
							// Two columns: the 8.3 short name, then the recovered full name when
							// resolved, otherwise the partial `?` pattern. The middle pattern
							// column is redundant once a name is recovered, so it is dropped.
							col2 := fp
							if fnr != "" {
								col2 = ff
							}
							short := br.file + br.tilde + br.ext
							dedupKey := ""
							if fnr != "" && match.collisionGroup != "" && !match.ordinalVerified {
								dedupKey = match.collisionGroup + "\x00" + strings.ToLower(fnr)
							}
							bufferEnum(ac, short, dedupKey, fmt.Sprintf("%-20s %s", short, col2), resolvedLong)
							progress.incFound()
						} else {
							o := resultOutput{
								Type:              "result",
								FullMatch:         resolvedLong,
								BaseUrl:           resultBaseURL,
								File:              br.file,
								Tilde:             br.tilde,
								Ext:               br.ext,
								Partname:          fn + fe,
								Fullname:          fnr,
								MatchType:         match.matchType,
								Status:            match.status,
								CollisionGroup:    match.collisionGroup,
								Oracle:            match.oracle,
								Method:            match.method,
								ProbeSuffix:       match.suffix,
								Checksum:          match.checksum,
								DerivedFrom:       match.derivedFrom,
								CandidateFamilies: match.families,
								DetectionOracle:   detectionOracle,
								DetectionMethod:   detectionMethod,
								DetectionSuffix:   detectionSuffix,
								DetectionStatus:   detectionStatus,
							}
							if fnr != "" {
								o.OrdinalVerified = boolPointer(match.ordinalVerified)
								o.SensitiveReason = sensitiveReason
							} else if br.ext == "" && (args.Auto || args.Full) {
								// Same auto-dirconfirm signal as the human branch (see there for
								// the full rationale) — structured-output consumers get the same
								// [DIR] information via a dedicated field instead of a rendered tag.
								o.DirectoryConfirmed = autoDirConfirmDirectory(hc, st, br.url, br.file+br.tilde)
							}
							printJSON(o)
						}
					} else if err == nil && len(br.ext) > 0 {
						if args.RelaxMatch {
							log.WithFields(log.Fields{"status": res.StatusCode, "statusNeg": mk.statusNeg, "filename": br.file + br.tilde + br.ext + profile.suffix}).
								Info("Tentative match (status matches negative)")
							fn, fe := br.file, br.ext
							if len(fn) >= 6 {
								fn = fn + "?"
							}
							if len(fe) >= 4 {
								fe = fe + "?"
							}
							if args.Output == "human" {
								var fp string
								if len(br.file) < 6 {
									fn = color.YellowString(fn)
								}
								if len(br.ext) < 4 {
									fe = color.YellowString(fe)
								}
								fp = strings.Replace(fn+fe, "?", color.HiBlackString("?"), -1)
								bufferTentativeEnum(ac, br.file+br.tilde+br.ext, fmt.Sprintf("%-20s %s %s", br.file+br.tilde+br.ext, fp, color.YellowString("[tentative]")))
							} else {
								printJSON(resultOutput{
									Type:            "result",
									FullMatch:       false,
									Tentative:       true,
									BaseUrl:         br.url,
									File:            br.file,
									Tilde:           br.tilde,
									Ext:             br.ext,
									Partname:        fn + fe,
									Fullname:        "",
									DetectionOracle: detectionOracle,
									DetectionMethod: detectionMethod,
									DetectionSuffix: detectionSuffix,
									DetectionStatus: detectionStatus,
								})
							}
						} else {
							log.WithFields(log.Fields{"status": res.StatusCode, "statusNeg": mk.statusNeg, "filename": br.file + br.tilde + br.ext + profile.suffix}).
								Debug("Possible hit, but status is the same as a negative match")
						}
					}
				}
				continueProfileEnumeration(sem, wg, hc, st, ac, profile, br, extMode)
			}
		}(sem, wg, hc, ac, profile, mk, br, string(char))
	}
}

// matrixProbeResult is one (suffix, method) combo's outcome from the
// vulnerability-detection matrix, returned by probeOracleCombo instead of
// mutated in shared state so several combos can run concurrently and the
// caller decides — in fixed priority order — which result wins.
type matrixProbeResult struct {
	suffix         string
	method         string
	statusPos      int
	statusNeg      int
	markersByTilde map[string]markers
	tildes         []string
	flapped        bool
}

// probeOracleCombo runs one (method, suffix) combo of the vulnerability-detection
// matrix: calibrate a stable negative baseline over 4 random-path probes, then
// test ~1..~4 against it, applying the same transient-status and ~0 catch-all
// guards the original sequential loop used. Side-effect-free apart from
// hc/st, so probeOracleCombo calls for different combos can run concurrently.
func probeOracleCombo(hc *http.Client, st *httpStats, url, method, suffix string) matrixProbeResult {
	var statusNeg int
	for i := 0; i < 4; i++ {
		res, err := fetch(hc, st, method, fmt.Sprintf("%s*%d*%s", url, rand.Intn(5)+5, suffix))
		if err != nil {
			log.Debug("Method " + method + " failed, skipping")
			return matrixProbeResult{}
		}
		status := res.StatusCode
		// A 5xx-gateway / 429 baseline is a flapping/unavailable front end
		// (CDN/LB/WAF), not IIS answering — it can never anchor an existence
		// oracle, and mixing it with real statuses is what fabricates a
		// phantom positive. Skip the method and remember to warn.
		if isTransientInfraStatus(status) {
			log.WithFields(log.Fields{"status": status, "method": method}).Debug("Baseline hit a 5xx/429 gateway status, skipping method")
			return matrixProbeResult{flapped: true}
		}
		if statusNeg != 0 && status != statusNeg {
			log.WithFields(log.Fields{"status": status, "statusNeg": statusNeg}).Debug("Method " + method + " unstable, skipping")
			return matrixProbeResult{}
		}
		statusNeg = status
	}
	result := matrixProbeResult{
		suffix: suffix, method: method, statusNeg: statusNeg,
		markersByTilde: make(map[string]markers),
	}
	for i := 1; i <= 4; i++ {
		res, err := fetch(hc, st, method, fmt.Sprintf("%s*%s%d*%s", url, tildify("~"), i, suffix))
		if err != nil {
			continue
		}
		statusPos := res.StatusCode
		// A 5xx-gateway / 429 is a flapping backend, never a real short-name
		// hit; accepting it as the positive status is the exact false-oracle
		// bug (statusPos=503 vs statusNeg=404).
		if isTransientInfraStatus(statusPos) {
			result.flapped = true
			continue
		}
		if statusPos == statusNeg {
			continue
		}
		// ~0 can't exist (ordinals start at ~1); if it answers the same as ~i
		// the server matches everything (rate limit / catch-all). fetch
		// returns a nil response on a transport error (common under
		// --parallel load) and res.StatusCode would nil-deref, so guard err0
		// and, on failure, trust the positive ~i signal (a real catch-all is
		// still caught later by the character-fraction guard).
		res0, err0 := fetch(hc, st, method, fmt.Sprintf("%s*%s0*%s", url, tildify("~"), suffix))
		if err0 == nil && statusPos == res0.StatusCode {
			log.WithFields(log.Fields{"statusPos": statusPos, "statusNeg": statusNeg}).Debug("Negative response differed, could be rate limiting or server instability")
			continue
		}
		// Re-verify the negative baseline before trusting the differential. The
		// 4-probe calibration above can lock onto a status that was only stable in
		// a burst (seen live: a target whose DEBUG verb bounces 400/500, so 4
		// straight 500s paired against a 400 positive fabricate a phantom oracle).
		// Re-probing the negative shape and requiring it to STILL answer statusNeg
		// every time rejects that flap while keeping a genuinely stable oracle
		// whose baseline happens to be a 500 (seen live on a different target:
		// DEBUG neg=500, pos=404 — real).
		if !negativeBaselineStable(hc, st, url, method, suffix, statusNeg) {
			log.WithFields(log.Fields{"statusPos": statusPos, "statusNeg": statusNeg, "method": method}).Debug("Negative baseline flapped on re-verify; rejecting phantom oracle")
			result.flapped = true
			continue
		}
		tilde := fmt.Sprintf("~%d", i)
		result.tildes = append(result.tildes, tilde)
		result.markersByTilde[tilde] = markers{statusPos: statusPos, statusNeg: statusNeg}
		result.statusPos = statusPos
	}
	return result
}

// calibrateAltStatusOracle attempts to build a status oracle using the WebDAV/extended
// HTTP verbs the primary matrix skips at patience 0 (PROPFIND, SEARCH, …) when GET/POST/
// OPTIONS/… yielded no tilde hits — the case of a front end that mutes the common verbs
// but still lets a WebDAV verb reach IIS's 8.3 existence check. The caller passes only
// methods the primary matrix did NOT already test; re-probing covered verbs adds nothing.
// Returns true if a viable oracle was found; populates ac.method, ac.suffix, ac.tildes, and mk fields.
// timedOut is Scan's per-URL --maxtime closure, passed in because this is a package-level
// helper and cannot see that Scan-local closure directly.
func calibrateAltStatusOracle(url string, hc *http.Client, st *httpStats, ac *attackConfig, mk *markers, methods, suffixes []string, timedOut func() bool) bool {
	for _, suffix := range suffixes {
		for _, method := range methods {
			if timedOut() {
				return false
			}
			var statusNeg int
			// Calibrate statusNeg with 4 stable probes on random paths.
			for i := 0; i < 4; i++ {
				res, err := fetch(hc, st, method, fmt.Sprintf("%s*%d*%s", url, rand.Intn(5)+5, suffix))
				if err != nil {
					log.WithField("method", method).Debug("Alt method failed during calibration")
					goto nextMethod
				}
				// Reject transient gateway statuses (flapping front end).
				if isTransientInfraStatus(res.StatusCode) {
					log.WithFields(log.Fields{"method": method, "status": res.StatusCode}).Debug("Alt method calibration hit gateway status")
					goto nextMethod
				}
				// Require stable statusNeg across all 4 probes.
				if statusNeg != 0 && res.StatusCode != statusNeg {
					log.WithField("method", method).Debug("Alt method unstable calibration")
					goto nextMethod
				}
				statusNeg = res.StatusCode
			}

			// Now try tilde probes with this (method, suffix, statusNeg).
			for i := 1; i <= 4; i++ {
				res, err := fetch(hc, st, method, fmt.Sprintf("%s*%s%d*%s", url, tildify("~"), i, suffix))
				if err != nil {
					continue
				}
				statusPos := res.StatusCode
				// Reject transient statuses on the positive side too.
				if isTransientInfraStatus(statusPos) {
					continue
				}
				// Check for a real status differential.
				if statusPos != statusNeg {
					// Verify ~0 doesn't match (catch-all guard).
					res0, err0 := fetch(hc, st, method, fmt.Sprintf("%s*%s0*%s", url, tildify("~"), suffix))
					if err0 == nil && statusPos == res0.StatusCode {
						log.WithFields(log.Fields{"method": method, "status": statusPos}).Debug("Alt method ~0 catch-all detected")
						continue
					}
					// Hit! Record and return.
					ac.tildes = []string{fmt.Sprintf("~%d", i)}
					ac.method = method
					ac.suffix = suffix
					mk.statusPos = statusPos
					mk.statusNeg = statusNeg
					return true
				}
			}
		nextMethod:
		}
	}
	return false
}

// Scan starts enumeration of the given URLs.
// A shared "visited" map is passed so that no URL is processed more than once.
func Scan(urls []string, hc *http.Client, st *httpStats, wc *wordlistConfig, mk markers, visited map[string]struct{}) {
	initialMarkers := mk
	siblingStems := newSiblingStemKnowledge()
	references := newReferenceKnowledge()
	sourceHits := &sourceHitStore{}     // per-scan; drained by runSourceAutoChain after the loop
	pathInfoHits := &pathInfoHitStore{} // per-scan; drained into the end-of-scan summary
	referenceCrawlers := make(map[string]*referenceCrawler)
	autoBitmapVisited := make(map[string]struct{})
	autoBitmapUnavailableOrigins := make(map[string]struct{})
	// indexChainSweptOrigins/indexChainSignalOrigins gate the reserved-folder
	// ::$INDEX_ALLOCATION sweep (indexChainURLs below), mirroring
	// runAutoBitmapProfiles' unavailableOrigins pattern: an origin that has NEVER
	// shown any 8.3 oracle signal (len(ac.tildes) > 0, anywhere, including via the
	// alt-oracle escalation) pays for exactly one reserved-folder sweep, not one per
	// directory. Deliberately origin-scoped, not directory-scoped: the sweep still
	// always runs on the FIRST directory tried per origin — and on every later
	// directory the moment that origin shows ANY signal — because a boring visible
	// directory can still hide a reserved folder underneath it (see the sweep site's
	// own comment); only a host that never once demonstrates oracle capability at
	// all gets capped, instead of independently re-paying the full ~9x
	// (root + reserved folders) matrix cost on every directory --full recurses into.
	indexChainSweptOrigins := make(map[string]struct{})
	indexChainSignalOrigins := make(map[string]struct{})
	// The user's autocomplete setting; "auto" must be re-resolved PER HOST — mutating
	// the global once leaked the first host's decision to every later URL in a --list.
	userAutocomplete := args.Autocomplete
	// Tracks the last-printed Running:/Active: signature — see the print site below.
	lastAnnounced := ""
	// True until the first directory's result (of either shape) has printed —
	// a vulnerable block supplies its own leading blank line, but the one-line
	// non-vulnerable case doesn't, so if the very first directory in the queue
	// turns out clean, it would otherwise butt up against the banner.
	firstBlock := true
	// True when the most recently-finished vulnerable block printed at least
	// one section (attackConfig is recreated fresh each loop iteration, so
	// this is how that fact survives into the possibly-many one-line
	// "Vulnerable: No" iterations for the directories queued right after it —
	// see the sectionRule print site below).
	lastPrintedWasContent := false
	processed := 0
	scanStart := time.Now()
	// scanTimedOut reports whether this URL's --maxtime budget is spent. Checked at the
	// per-directory loop head and inside the sequential vulnerability-detection matrix
	// (the two long poles); concurrent phases are already bounded by -t/-c per request.
	scanTimedOut := func() bool {
		return args.MaxTime > 0 && time.Since(scanStart) > time.Duration(args.MaxTime)*time.Second
	}
	// Main loop while there are URLs in the queue
	for len(urls) > 0 {
		if scanTimedOut() {
			// Never truncate silently: --maxtime tripped with paths still queued,
			// so say so instead of printing a clean "Finished!" that reads as a
			// complete scan. Default is 0 (no limit), so this only fires when the
			// user opted in.
			if remaining := len(urls); remaining > 0 {
				log.WithFields(log.Fields{"maxtime": args.MaxTime, "queued": remaining}).Warn("--maxtime reached; stopping with paths still queued")
				printHuman(color.HiYellowString("⚠ --maxtime %ds reached — stopped with %d queued path(s) unscanned (raise --maxtime, or set 0 to disable the limit)", args.MaxTime, remaining))
			}
			break
		}
		var url string
		url, urls = urls[0], urls[1:]
		url = strings.TrimSuffix(url, "/") + "/"
		// Markers are directory-local calibration state. Reusing a header or
		// status class from the previous queue entry can fabricate a profile for
		// a later URL whose only signal is an unrelated fallback.
		mk = initialMarkers

		// Skip if URL has already been visited. IIS/NTFS paths are
		// case-insensitive, so dedup case-insensitively too — otherwise a
		// directory two different recovery paths report in different casing
		// (e.g. WebDAV's on-disk "aspnet_client" vs the 8.3 wordlist's
		// canonical "ASPNET_CLIENT") gets scanned twice, and everything
		// recursively found under each casing gets scanned twice again,
		// compounding at each level.
		visitKey := strings.ToLower(url)
		if _, ok := visited[visitKey]; ok {
			continue
		}
		visited[visitKey] = struct{}{}
		processed++
		progress.setDir(url)
		progress.setQueue(processed, processed+len(urls))
		progress.setPhase("checking")

		// Default to HTTPS if no protocol is provided
		if !strings.Contains(url, "://") {
			url = "https://" + url
		}
		// --custom-sfn combined with a scan (--auto/--full/-r): probe each supplied
		// custom short-name alias for a content read at every scanned directory.
		if len(args.CustomSFN) > 0 {
			progress.setPhase("custom-sfn")
			for _, alias := range args.CustomSFN {
				probeCustomSFN(hc, st, url, strings.TrimPrefix(alias, "/"))
			}
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

		srv := "<unknown>"
		if len(res.Header["Server"]) > 0 {
			srv = strings.Join(res.Header["Server"], ", ")
		}
		if v, ok := res.Header["X-Aspnet-Version"]; ok {
			srv += " (ASP.NET v" + v[0] + ")"
		}
		nonIIS := srv != "<unknown>" && !strings.Contains(srv, "IIS") && !strings.Contains(srv, "ASP")
		if args.Output == "human" && nonIIS {
			srv += " " + color.HiRedString("[!]")
		}

		// Set up autocomplete mode — re-resolve per host from the user's setting so a
		// multi-host --list scan does not inherit the first host's detected mode. This
		// resolves into a LOCAL variable (stored on ac below), never back into the
		// shared args.Autocomplete global: --parallel runs one goroutine per host, and
		// that global write used to race across hosts (see the attackConfig.autocomplete
		// doc comment).
		resolvedAutocomplete := userAutocomplete
		if resolvedAutocomplete == "auto" {
			// Pick method-magic when the invalid-method probe answers 405 (= the root
			// resource exists). Reliability against 405-for-everything servers is no
			// longer decided here by switching the whole oracle to status — instead
			// probeAutocompleteCandidate validates each 405 against a same-extension
			// baseline, so hidden files are kept in the dimensions where 405 is real.
			if res, err := fetch(hc, st, "_", url); err == nil && res.StatusCode == 405 {
				resolvedAutocomplete = "method"
				log.Info("Using method-based file existence checks (405 validated per-extension against a baseline)")
			} else {
				resolvedAutocomplete = "status"
				log.Info("Using status-based file existence checks")
			}
		}

		// First stage: check if the server is vulnerable
		ac := attackConfig{autocomplete: resolvedAutocomplete, wordlist: wc, siblingStems: siblingStems, references: references, sourceHits: sourceHits, pathInfoHits: pathInfoHits}
		var pc, mc int
		if args.Patience == 1 {
			pc = len(pathSuffixes)
			mc = len(httpMethods)
		} else {
			pc = 4
			mc = 9
		}
		flappingFrontend := false
		type oracleCombo struct{ suffix, method string }
		combos := make([]oracleCombo, 0, pc*mc)
		for _, suffix := range pathSuffixes[:pc] {
			for _, method := range httpMethods[:mc] {
				combos = append(combos, oracleCombo{suffix, method})
			}
		}
		// Discovery uses fixed logical windows so -c controls only scheduling, not
		// which profiles exist. Default mode stops after the first winning window;
		// --patience 1 deliberately walks every window to build the full portfolio.
		const windowSize = 4
		requestParallel := args.Concurrency
		if requestParallel < 1 {
			requestParallel = 1
		}
	combosLoop:
		for start := 0; start < len(combos); start += windowSize {
			if scanTimedOut() {
				break combosLoop
			}
			end := start + windowSize
			if end > len(combos) {
				end = len(combos)
			}
			batch := combos[start:end]
			results := make([]matrixProbeResult, len(batch))
			var wg sync.WaitGroup
			probeSem := make(chan struct{}, requestParallel)
			for i, c := range batch {
				wg.Add(1)
				go func(i int, c oracleCombo) {
					defer wg.Done()
					probeSem <- struct{}{}
					defer func() { <-probeSem }()
					results[i] = probeOracleCombo(hc, st, url, c.method, c.suffix)
				}(i, c)
			}
			wg.Wait()
			for _, r := range results {
				if r.flapped {
					flappingFrontend = true
				}
			}
			if installBatchOracleProfiles(&ac, &mk, results) && args.Patience != 1 {
				// Default mode bounds calibration at the first logical window with a
				// signal. Patience mode keeps collecting later methods/suffixes.
				break combosLoop
			}
		}

		// A front end that flaps 5xx/429 into otherwise-real statuses can't anchor
		// the oracle; we refused to build a phantom positive from it. Say so, so the
		// operator reads "unreliable front end" instead of "no 8.3" — and doesn't get
		// the hundreds of never-resolving garbage names this used to emit.
		if flappingFrontend && len(ac.tildes) == 0 {
			printHuman(color.HiYellowString("⚠ flapping front end (CDN/LB/WAF): probes bounced between 5xx/429 and real statuses — 8.3 oracle suppressed to avoid false names. Retry on the origin, or lower --concurrency / raise --delay."))
		} else if flappingFrontend {
			// A stable oracle was still found on a later combo, so the result below is
			// real — but some earlier combo on this same host DID see the front end
			// flap, and that instability doesn't just vanish. Softer than the outright
			// suppression warning above: treat the finding as usable, just less certain.
			printHuman(color.HiYellowString("⚠ front end showed transient 5xx/429 on other probe(s) for this host — the oracle below still calibrated cleanly, but treat the result as less certain than usual."))
		}

		// --auto/--full -i: /bin, App_Code and App_Data are requestFiltering
		// hiddenSegments, so a direct GET on them (or recursion into them) always
		// misses — that's precisely the case the ::$INDEX_ALLOCATION oracle exists
		// to reach around. Computed and enqueued here, before the not-vulnerable
		// early-continue below, so scanning a reserved folder directly (or a
		// directory that hides one) still queues its ADS probe instead of the
		// sweep being skipped because the visible directory itself found nothing.
		//
		// Gated per-origin (not per-directory): the first directory tried on an
		// origin always gets the sweep; a later directory only skips it if this
		// origin has ALREADY been swept at least once AND has never once shown any
		// oracle signal (indexChainSignalOrigins, updated after the alt-oracle
		// escalation below) — see the field doc comment above for why this can't be
		// "skip whenever the current directory is empty" without breaking the
		// hidden-reserved-folder case the comment above already defends against.
		chainOrigin := originKey(url)
		_, chainAlreadySwept := indexChainSweptOrigins[chainOrigin]
		_, chainOriginHasSignal := indexChainSignalOrigins[chainOrigin]
		var chain []string
		if !chainAlreadySwept || chainOriginHasSignal {
			chain = indexChainURLs(url)
			if len(chain) > 0 {
				urls = append(chain, urls...)
				indexChainSweptOrigins[chainOrigin] = struct{}{}
			}
		}

		// Alt-oracle fallback: only under --auto/--full, and only when the primary
		// matrix skipped verbs (patience 0 → mc=9). The default matrix already tests
		// OPTIONS/HEAD/TRACE/DEBUG/GET/POST/PUT/PATCH/DELETE, so re-probing those adds
		// nothing — the value is in the WebDAV verbs it skips, for a front end that
		// mutes the common verbs but lets a WebDAV verb reach IIS's 8.3 check. Patience 1
		// already tests every verb (mc == len(httpMethods)), so there is nothing to escalate to.
		if len(ac.tildes) == 0 && !flappingFrontend && (args.Auto || args.Full) && mc < len(httpMethods) {
			altMethods := []string{"PROPFIND", "SEARCH", "PROPPATCH", "MKCOL", "LOCK"}
			log.Debug("Primary oracle produced no hits; escalating to WebDAV verbs")
			if calibrateAltStatusOracle(url, hc, st, &ac, &mk, altMethods, pathSuffixes[:pc], scanTimedOut) {
				log.WithFields(log.Fields{"method": ac.method, "suffix": ac.suffix}).Info("Alt-oracle succeeded")
			}
		}

		// A status-normalising edge can erase every status differential while
		// still forwarding categorical origin headers. Unlike the PROPFIND body
		// fallback below, this calibrated signature is usable throughout charset
		// discovery and enumeration, so it recovers names rather than only
		// reporting that an oracle probably exists.
		if len(ac.tildes) == 0 && !flappingFrontend && (args.Auto || args.Full) {
			headerMethods := []string{"OPTIONS", "HEAD", "TRACE", "DEBUG", "GET", "PROPFIND", "MKCOL", "PROPPATCH"}
			if calibrateHeaderOracle(url, hc, st, &ac, &mk, headerMethods, pathSuffixes[:pc], scanTimedOut) {
				log.WithFields(log.Fields{"method": ac.method, "suffix": ac.suffix}).Info("Header-signature oracle succeeded")
			}
		}

		// Tier B last resort: every status-based oracle (primary matrix + WebDAV-verb
		// escalation) came up empty. Try a PROPFIND body-content differential —
		// detection-only (see sizeoracle.go), so it only fires when nothing else did.
		if len(ac.tildes) == 0 && !flappingFrontend && (args.Auto || args.Full) {
			if calibrateSizeOracle(url, hc, st, &ac, pathSuffixes[:pc], scanTimedOut) {
				log.WithField("suffix", ac.suffix).Info("Size-oracle succeeded (PROPFIND body differential, detection-only)")
			}
		}
		ensureLegacyOracleProfile(&ac, mk)
		// Record this origin's final (post-alt-oracle) signal for the reserved-folder
		// sweep gate above: a future directory on the same origin is only allowed to
		// skip a repeat sweep once this origin has shown NO signal anywhere, so a hit
		// here — however it was found — must be visible to the next iteration.
		if len(ac.tildes) > 0 {
			indexChainSignalOrigins[chainOrigin] = struct{}{}
		}

		// Fingerprint/status must describe the FINAL oracle result, including the
		// WebDAV, header-signature and body fallbacks above. Emitting them before
		// those fallbacks produced the contradictory "8.3 oracle: no" followed by
		// "Vulnerable: Yes" on exactly the hardened edges these paths support.
		if args.Fingerprint {
			runFingerprint(url, hc, st, len(ac.tildes) > 0, srv, nonIIS)
		}

		// --auto/--full: once per host, check the http.sys request-smuggling desync
		// preconditions (h1 TE.CL/bare-LF, or h2 leniencies on https) — silent unless
		// a precondition is found. Gated to IIS-ish hosts (a masking front end is the
		// point, but a totally non-IIS host has no http.sys to test). Explicit
		// --desync-probe stays available for full per-variant detail on any host.
		if (args.Auto || args.Full) && (len(ac.tildes) > 0 || strings.Contains(strings.ToLower(srv), "iis")) {
			runDesyncAuto(url, st)
		}

		detectionOracle := ac.detectionOracle
		detectionMethod, detectionSuffix := ac.method, ac.suffix
		profileCount := len(ac.oracleProfiles)
		if profileCount > 0 {
			primary := ac.oracleProfiles[0]
			detectionOracle, detectionMethod, detectionSuffix = primary.detectionOracle, primary.method, primary.suffix
		} else if len(ac.tildes) > 0 {
			// Detection-only body-distance is a real signal but intentionally has
			// no enumerable marker profile.
			profileCount = 1
		}
		if detectionOracle == "" && len(ac.tildes) > 0 {
			detectionOracle = "status"
		}
		printJSON(statusOutput{
			Type: "status", Url: url, Server: srv, Vulnerable: len(ac.tildes) > 0,
			Oracle: detectionOracle, Method: detectionMethod, ProbeSuffix: detectionSuffix, ProfileCount: profileCount,
		})

		if len(ac.tildes) == 0 {
			// Reserved-folder ::$INDEX_ALLOCATION probes are speculative internal
			// chain steps (bin/App_Code/App_Data/App_* under --auto -i / --full);
			// a "Vulnerable: No" on each just walls the screen (8+ per host) with
			// no signal. Suppress them unless verbose — the real directories still
			// print their verdict.
			if args.Verbosity == 0 && strings.Contains(strings.ToUpper(url), "INDEX_ALLOCATION") {
				continue
			}
			if bulkCompact() {
				// Compact bulk: one header line + the one-line fingerprint, nothing else.
				printHumanHostHeader(compactHostHeader(url, false, "", nonIIS))
				if o, ok := takeHostFingerprint(); ok {
					printHuman(color.HiBlackString(fingerprintCompactLine(o)))
				}
				continue
			}
			if firstBlock {
				printHuman()
			}
			firstBlock = false
			// One divider before the whole run of these, not one per line —
			// consumed on the first line so the rest of a consecutive run
			// stays tight.
			if lastPrintedWasContent {
				printHuman(sectionRule)
				lastPrintedWasContent = false
			}
			printHuman(nonVulnerableLine(url, nonIIS))
			continue
		}
		firstBlock = false
		vulnerableCountMu.Lock()
		vulnerableCount++
		vulnerableCountMu.Unlock()

		// The full header block (rule / URL / Running / Active / Vulnerable) is
		// only worth showing for a directory that actually has something to
		// report — everything else gets the one-line treatment above. Running:/
		// Active: describe the server and this run's toggles, not the
		// directory, so recursing into many directories on the same server
		// would otherwise reprint the identical two lines on every block; only
		// show them again when the server (or the active toggles) changed
		// since the last block that printed them.
		if bulkCompact() {
			// Compact bulk: one header line with the verdict + the one-line
			// fingerprint; the findings that follow are indented under it at flush.
			printHumanHostHeader(compactHostHeader(url, true, ac.autocomplete, nonIIS))
			if o, ok := takeHostFingerprint(); ok {
				printHuman(color.HiBlackString(fingerprintCompactLine(o)))
			}
		} else {
			printHuman("\n════════════════════════════════════════════════════════════════════════════════")
			printHuman(color.New(color.FgWhite, color.Bold).Sprint("URL")+":", url)
			modes := activeModes(ac.autocomplete)
			if args.Output == "human" {
				signature := srv + "\x00" + strings.Join(modes, "\x00")
				if signature != lastAnnounced {
					lastAnnounced = signature
					if !args.Fingerprint { // the Fingerprint block already states the Server
						printHuman(color.New(color.FgWhite, color.Bold).Sprint("Running")+":", srv)
					}
					label := color.New(color.FgWhite, color.Bold).Sprint("Active:")
					if len(modes) == 0 {
						printHuman(label, color.HiBlackString("default enumeration (no recovery/probe toggles)"))
					} else {
						printHuman(label, color.HiCyanString(strings.Join(modes, " · ")))
					}
				}
			}
			printHuman(color.New(color.FgWhite, color.Bold).Sprint("Vulnerable:"), color.HiRedString("Yes!")+oracleNote(ac.autocomplete, ac.method, ac.detectionOracle))
			printHuman(headerRule)
			printHuman()
		}
		// Alt-oracle recovery-degradation warning: 8.3 detection via a WebDAV verb
		// means the front end likely mutes the common verbs, but long-name recovery
		// still probes with the GET-based autocomplete oracle — so on a fully-muted-GET
		// front end it can resolve nothing even though the enumerated 8.3 names are
		// valid. allow-copy recovery is already PROPFIND-based, so it needs no warning.
		if isWebDAVDetectionVerb(ac.method) && ac.autocomplete != "allow-copy" && ac.autocomplete != "none" {
			printHuman(color.HiYellowString("⚠ 8.3 detection used %s — the front end appears to mute the common verbs. Long-name recovery still probes with the %s oracle (%s); if that verb is muted it may resolve nothing though the short names are valid. Retry with -a allow-copy for PROPFIND-based recovery.", ac.method, ac.autocomplete, autocompleteProbeMethod(ac.autocomplete)))
		}
		log.WithFields(log.Fields{"method": ac.method, "suffix": ac.suffix, "statusPos": mk.statusPos, "statusNeg": mk.statusNeg, "detectionOracle": ac.detectionOracle}).Info("Found working options")
		log.WithFields(log.Fields{"tildes": ac.tildes}).Info("Found tilde files")
		if args.IsVuln {
			continue
		}
		var crawler *referenceCrawler
		var initialCrawlDone chan referenceCrawlStats
		if args.CrawlReferences {
			origin := originKey(url)
			crawler = referenceCrawlers[origin]
			newCrawler := false
			if crawler == nil {
				crawler = newReferenceCrawler(references, args.CrawlMaxPages, args.CrawlMaxDepth, args.CrawlBodyLimit)
				referenceCrawlers[origin] = crawler
				newCrawler = true
			}
			initialCrawlDone = make(chan referenceCrawlStats, 1)
			seeds := []string{url}
			if newCrawler {
				seeds = append(seeds, args.CrawlSeeds...)
			}
			go func() {
				initialCrawlDone <- crawler.crawl(hc, st, url, seeds)
			}()
		}
		needsWordlist := needsConfiguredWordlist(ac.autocomplete)
		if args.ReferenceOnly {
			ac.wordlist = nil
		}
		if needsWordlist && wc != nil {
			log.WithField("sources", len(wc.sources)).Info("Starting deferred wordlist load")
			wc.startLoading()
		}

		// Second stage: determine which characters are in use. These ~2×len(Characters)
		// probes used to run one blocking request at a time — the bulk of the wait
		// before the first enumeration result ("time to first byte"). Fire them
		// concurrently (bounded by -c) exactly like stage three: same probes and same
		// resulting character set, only the scheduling changes. Rebuild each set in
		// args.Characters order afterwards so the alphabet stays deterministic.
		progress.setPhase("charset")
		activeProfiles := make([]oracleProfile, 0, len(ac.oracleProfiles))
		for i := range ac.oracleProfiles {
			profile := &ac.oracleProfiles[i]
			fileFrac, extFrac := discoverProfileChars(hc, st, url, profile)
			if fileFrac > catchAllThreshold {
				printHuman(color.HiYellowString("⚠ catch-all / soft-response profile %s %q (%.0f%% of charset) — this profile was discarded.", profile.method, profile.suffix, fileFrac*100))
				log.WithFields(log.Fields{"url": url, "method": profile.method, "suffix": profile.suffix, "matchedFraction": fileFrac}).Warn("Catch-all profile discarded")
				continue
			}
			if extFrac > catchAllThreshold {
				printHuman(color.HiYellowString("⚠ catch-all extension profile %s %q (%.0f%% of charset) — extensions skipped only for this profile.", profile.method, profile.suffix, extFrac*100))
				for _, tilde := range profile.tildes {
					profile.extChars[tilde] = ""
				}
			}
			activeProfiles = append(activeProfiles, *profile)
		}
		ac.oracleProfiles = activeProfiles
		rebuildMergedProfileChars(&ac)
		log.WithFields(log.Fields{"profileCount": len(ac.oracleProfiles), "fileChars": ac.fileChars, "extChars": ac.extChars}).Info("Built profile-isolated character sets")
		if len(ac.oracleProfiles) == 0 {
			printHuman(color.HiYellowString("⚠ every calibrated 8.3 profile behaved as catch-all — enumeration suppressed."))
			continue
		}

		// Third stage: full enumeration
		if needsWordlist && wc != nil {
			if err := wc.waitLoaded(); err != nil {
				log.WithFields(log.Fields{"err": err}).Error("Unable to load wordlist; continuing without long-name recovery")
				ac.wordlist = nil
			} else {
				log.WithFields(log.Fields{
					"entries": wc.loadStats.entries, "files": wc.loadStats.files,
					"duplicates": wc.loadStats.duplicates, "rainbow_replacements": wc.loadStats.replaced,
					"duration": wc.loadStats.duration,
				}).Info("Deferred wordlist load complete")
			}
		}
		if initialCrawlDone != nil {
			reportReferenceCrawl(&ac, <-initialCrawlDone, "initial")
		}
		ac.foundFiles = make(map[string]struct{})
		ac.foundDirectories = make(map[string]struct{})
		progress.setPhase("enumerating")
		sem := make(chan struct{}, args.Concurrency)
		for i := range ac.oracleProfiles {
			profile := &ac.oracleProfiles[i]
			wg := new(sync.WaitGroup)
			for _, tilde := range profile.tildes {
				enumerate(sem, wg, hc, st, &ac, profile, baseRequest{url: url, file: "", tilde: tilde, ext: ""})
			}
			wg.Wait()
		}
		if len(ac.enumEntries) > 0 {
			beginSection(&ac)
			shown, resolved := collapseEnumEntries(ac.enumEntries)
			printHuman(color.HiCyanString("[SHORTNAMES] %d/%d resolved to full name", resolved, len(shown)))
			for _, line := range shown {
				printHuman(line)
			}
		}
		// Now on the main goroutine (all enumerate workers joined): flush the
		// side-findings they buffered so they land in this host's block under
		// --parallel. A no-op in single-host / JSON runs (nothing was buffered).
		ac.flushDeferredFindings()
		if crawler != nil {
			progress.setPhase("crawling")
			var crawlStats referenceCrawlStats
			maxRounds := args.CrawlMaxDepth + 2
			if args.Loop {
				maxRounds = 12
				if args.LoopMax > 0 {
					maxRounds = args.LoopMax
				}
			}
			for round := 0; round < maxRounds; round++ {
				seeds := takeReferenceSeeds(&ac)
				if len(seeds) > 0 {
					crawlStats = mergeReferenceCrawlStats(crawlStats, crawler.crawl(hc, st, url, seeds))
				}
				recovered := recoverReferenceAliases(hc, st, &ac, scanTimedOut)
				if recovered > 0 {
					log.WithField("recovered", recovered).Info("Recovered long names from public HTML/JS/CSS references")
				}
				if len(seeds) == 0 && recovered == 0 {
					break
				}
			}
			reportReferenceCrawl(&ac, crawlStats, "follow-up")
		}
		progress.setPhase("sibling")
		if recovered := recoverSiblingAliases(hc, st, &ac, scanTimedOut); recovered > 0 {
			log.WithField("recovered", recovered).Info("Recovered long names from verified sibling stems")
		}
		progress.setPhase("collision-ancestry")
		if recovered := recoverCollisionAncestryAliases(hc, st, &ac, scanTimedOut); recovered > 0 {
			log.WithField("recovered", recovered).Info("Recovered long names from saturated collision-family ancestry")
		}

		// --webdav name-lift: after enumerating this directory, if it advertises
		// WebDAV, PROPFIND Depth:1 to recover the full long names (and flag the
		// requestFiltering-hidden ones) — a common lever past the 6+3 truncation.
		progress.setPhase("webdav-lift")
		runWebDAVLift(hc, st, &ac, url)

		// --tilde-continuation / --auto / --full: recover the full long name of any
		// file shaped `XXXXXX~<digit>...` by anchoring the oracle on the literal tilde.
		progress.setPhase("tilde-continuation")
		runTildeContinuation(hc, st, &ac, mk, url)

		// --brute: last resort, so it only spends its request budget on
		// aliases every cheaper technique above already failed to resolve.
		progress.setPhase("brute")
		if recovered := recoverStemBruteAliases(hc, st, &ac, scanTimedOut); recovered > 0 {
			log.WithField("recovered", recovered).Info("Recovered long names via short-suffix brute")
		}

		// Second drain: the post-enumeration recovery phases above (reference /
		// sibling / collision / brute) run their own worker pools, and a worker's
		// enrichResolvedFile can emitHuman a side-note (source disclosure, PathInfo
		// candidate). Those workers have no host sink, so emitHuman buffers them into
		// deferredFindings — which the 1st flush (before these phases) already passed.
		// Drain again here, on the main goroutine, so nothing is silently swallowed
		// under --parallel. A no-op when nothing was buffered.
		ac.flushDeferredFindings()

		bitmapHighWater := make(map[string]bool)
		if args.Auto || args.Full {
			progress.setPhase("bitmap")
			bitmapHighWater = runAutoBitmapProfiles(hc, st, &ac, url, chain,
				autoBitmapVisited, autoBitmapUnavailableOrigins)
		}

		// Prepend discovered directories for further processing, but only when
		// forward recursion is explicitly enabled (--recurse/-r).
		if args.Recurse {
			directories := make([]string, 0, len(ac.foundDirectories))
			for dir := range ac.foundDirectories {
				directories = append(directories, dir)
			}
			sort.SliceStable(directories, func(i, j int) bool {
				left := bitmapHighWater[strings.ToLower(url+directories[i]+"/")]
				right := bitmapHighWater[strings.ToLower(url+directories[j]+"/")]
				if left != right {
					return left
				}
				return strings.ToLower(directories[i]) < strings.ToLower(directories[j])
			})
			queued := make([]string, 0, len(directories))
			for _, dir := range directories {
				queued = append(queued, url+dir+"/")
			}
			urls = append(queued, urls...)
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
					if _, exists := visited[strings.ToLower(newURL)]; !exists {
						urls = append(urls, newURL)
						log.WithField("url", newURL).Debug("Added regressive scan URL")
					}
				}
			}
		}

		// Only reached by a vulnerable-block iteration (the non-vulnerable
		// branch above always `continue`s) — carry whether it printed any
		// section forward, for the compact "Vulnerable: No" lines that may
		// immediately follow it.
		lastPrintedWasContent = ac.sectionStarted
	}
	if args.Index || args.Full || args.Auto {
		runSourceAutoChain(hc, st, sourceHits)
	}
	if args.Output == "human" {
		runPathInfoSummary(pathInfoHits.drain())
	}
}
