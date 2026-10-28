package shortscan

import (
	"bytes"
	"fmt"
	"net/http"
	"regexp"
	"strings"
	"sync"

	"github.com/fatih/color"
)

// PATH_INFO consumption probe.
//
// IIS RequestFiltering (hiddenSegments/fileExtensions) keys on GetScriptName() and
// never inspects PATH_INFO (the URL tail after a script-mapped resource, e.g. the
// "/a/b" in "/handler.ashx/a/b"). That is by-design CGI semantics and harmless on
// its own: IIS does NOT serve the PATH_INFO path. It becomes an arbitrary-file-read
// (CWE-22, an APPLICATION bug — not an IIS bug) only when the handler itself does
// something like File.ReadAllText(Server.MapPath(Request.PathInfo)) without
// validation. This probe detects, black-box, whether a handler CONSUMES PathInfo as
// a filesystem path; when it finds a file-map signal it actively CONFIRMS the read
// by pulling the requestFiltering-blocked app-root web.config through the handler
// and reporting only a redacted signature (byte count + "<configuration> present" +
// the direct-block status) — it proves the bug without surfacing the secret bytes.
//
// Three oracles, all validated live, combined with controls so a broken/constant
// handler is not misreported:
//   1. illegal-FS-char differential (primary): a char that a URL allows but a
//      Windows path forbids (| " < > *) crashes MapPath/File.* -> 5xx, WHILE a
//      benign PathInfo stays non-5xx. The benign-not-5xx control rules out handlers
//      that 5xx on any PathInfo. (An edge that rejects the char yields 4xx, not
//      5xx, so it is not flagged.)
//   2. reflection: a random marker placed in PathInfo appears in a 2xx body (the
//      handler used it). Gated to 2xx so a custom error page echoing the URL does
//      not count.
//   3. physical-path leak: a drive-letter path (C:\...) in a response, corroborating
//      MapPath. Weighted as corroboration only (IIS detailed errors leak paths too).

// pathInfoHandlerExts are the extensions whose handlers populate Request.PathInfo
// and can map it to a file (the auto path only probes these; the standalone
// --pathinfo-probe accepts any URL the operator supplies).
var pathInfoHandlerExts = map[string]bool{
	".aspx": true, ".ashx": true, ".asmx": true, ".svc": true,
}

// drivePathRe matches a Windows drive-letter path leaked into a response body.
var drivePathRe = regexp.MustCompile(`[A-Za-z]:\\[^"'<>\r\n]{1,120}`)

// illegalPathInfoChars are URL-legal but Windows-path-ILLEGAL segment payloads; a
// handler that maps PathInfo to a path throws (5xx) on these.
var illegalPathInfoChars = []string{"a%7Cb", "a%22b"} // '|' and '"'

// hasPathInfoHandlerExt reports whether name ends in a PathInfo-capable handler ext.
func hasPathInfoHandlerExt(name string) bool {
	if i := strings.LastIndexByte(name, '.'); i >= 0 {
		return pathInfoHandlerExts[strings.ToLower(name[i:])]
	}
	return false
}

// appendPathInfo inserts "/tail" as a PATH_INFO segment into rawurl, BEFORE any
// query string, so a carrier URL that carries a query (e.g. download.ashx?id=1)
// still routes the tail into Request.PathInfo (download.ashx/tail?id=1) instead of
// burying it in the query where it never reaches the handler as PathInfo.
func appendPathInfo(rawurl, tail string) string {
	base, query := rawurl, ""
	if i := strings.IndexByte(rawurl, '?'); i >= 0 {
		base, query = rawurl[:i], rawurl[i:]
	}
	return strings.TrimRight(base, "/") + "/" + tail + query
}

type pathInfoVerdict struct {
	reachable     bool
	accepts       bool // handler still runs with a PathInfo tail (didn't 404 it)
	reflects      bool // marker echoed in a 2xx body
	mapsFile      bool // illegal-char 5xx differential -> maps PathInfo to a path
	physLeak      bool // drive-letter path leaked (corroboration)
	baseStatus    int
	benignStatus  int
	illegalStatus int
	confidence    string // none | low | medium | high | confirmed
	confirmed     bool   // read an RF-blocked file (web.config) via PathInfo
	confirmEvid   string // redacted proof (size + signature + direct-block status)
}

// classifyPathInfo runs the three oracles with controls and returns a verdict.
// ok is false only if the carrier is unreachable.
func classifyPathInfo(hc *http.Client, st *httpStats, url string) (pathInfoVerdict, bool) {
	var v pathInfoVerdict
	url = strings.TrimRight(url, "/")

	bres, _, berr := fetchBody(hc, st, "GET", url, 2048)
	if berr != nil || bres == nil {
		return v, false
	}
	v.reachable = true
	v.baseStatus = bres.StatusCode
	// A carrier that is itself 404 is not a live handler — nothing to probe.
	if v.baseStatus == http.StatusNotFound {
		v.confidence = "none"
		return v, true
	}

	marker := "sspi" + randAlnum(10)
	nres, nbody, nerr := fetchBody(hc, st, "GET", appendPathInfo(url, marker), 4096)
	if nerr != nil || nres == nil {
		return v, true
	}
	v.benignStatus = nres.StatusCode

	// Accepts PathInfo? A working carrier that 404s once a tail is appended did not
	// split into script-name + PathInfo (ext not script-mapped, or handler rejects
	// it) -> not a PathInfo-consuming target.
	if v.benignStatus == http.StatusNotFound && v.baseStatus != http.StatusNotFound {
		v.confidence = "none"
		return v, true
	}
	v.accepts = true

	if v.benignStatus/100 == 2 && bytes.Contains(bytes.ToLower(nbody), []byte(marker)) {
		v.reflects = true
	}

	illegal5xx := 0
	for _, ic := range illegalPathInfoChars {
		ires, ibody, ierr := fetchBody(hc, st, "GET", appendPathInfo(url, ic), 2048)
		if ierr != nil || ires == nil {
			continue
		}
		if ires.StatusCode/100 == 5 {
			illegal5xx++
			v.illegalStatus = ires.StatusCode // prefer a 5xx as the displayed illegal status
			// A drive-letter path in the EXCEPTION body is a genuine MapPath leak;
			// only count it here, not from a benign body that may just contain a path.
			if drivePathRe.Match(ibody) {
				v.physLeak = true
			}
		} else if v.illegalStatus == 0 {
			v.illegalStatus = ires.StatusCode
		}
	}
	// Primary signal, with the benign-not-5xx control: a handler that 5xx's on any
	// PathInfo is inconclusive, not a MapPath signal.
	if v.benignStatus/100 != 5 && illegal5xx > 0 {
		v.mapsFile = true
	}

	switch {
	case v.mapsFile && (v.physLeak || v.reflects):
		v.confidence = "high"
	case v.mapsFile:
		v.confidence = "medium"
	case v.reflects:
		v.confidence = "low"
	default:
		v.confidence = "none"
	}
	// When there is a file-map signal, actively CONFIRM it: read the RF-blocked
	// app-root web.config through the handler's PathInfo. A positive turns the
	// candidate into a proven read (and resolves the medium/high uncertainty).
	if v.mapsFile {
		if ok, ev := confirmPathInfoRead(hc, st, url); ok {
			v.confirmed, v.confirmEvid, v.confidence = true, ev, "confirmed"
		}
	}
	return v, true
}

// looksLikeWebConfig recognises a web.config-shaped body by structure alone, so the
// confirmation never has to inspect (or surface) the secret values inside it.
func looksLikeWebConfig(body []byte) bool {
	lo := bytes.ToLower(body)
	return bytes.Contains(lo, []byte("<configuration")) &&
		(bytes.Contains(lo, []byte("<system.web")) ||
			bytes.Contains(lo, []byte("<appsettings")) ||
			bytes.Contains(lo, []byte("<?xml")))
}

// confirmPathInfoRead does a bounded, read-only CONFIRMATION of the file-read
// primitive: it reads the app-root web.config THROUGH the handler's PathInfo and
// checks the same file is blocked on the direct path. It returns only a redacted
// signature (byte count + "<configuration> present" + the direct-block status),
// never the file's contents, so it proves the bug without dumping secrets.
func confirmPathInfoRead(hc *http.Client, st *httpStats, handlerURL string) (bool, string) {
	vres, vbody, verr := fetchBody(hc, st, "GET", appendPathInfo(handlerURL, "web.config"), 4096)
	if verr != nil || vres == nil || vres.StatusCode/100 != 2 || !looksLikeWebConfig(vbody) {
		return false, ""
	}
	// The same file must be blocked on the direct path — otherwise it is merely a
	// world-readable web.config, not a requestFiltering bypass.
	dres, _, derr := fetchBody(hc, st, "GET", schemeHost(handlerURL)+"/web.config", 512)
	if derr != nil || dres == nil || dres.StatusCode == http.StatusOK {
		return false, ""
	}
	return true, fmt.Sprintf("read app-root web.config via PathInfo (%d B, <configuration> present); /web.config blocked on the direct path (%d)", len(vbody), dres.StatusCode)
}

// runPathInfoProbe drives --pathinfo-probe: verbose per-URL oracle output.
func runPathInfoProbe(urls []string, hc *http.Client, st *httpStats) {
	var targets []string
	for _, u := range urls {
		for _, part := range strings.Split(u, ",") {
			if part = strings.TrimSpace(part); part != "" {
				targets = append(targets, part)
			}
		}
	}
	for _, url := range targets {
		printHuman(color.New(color.FgWhite, color.Bold).Sprint("[PATHINFO] "), url)
		v, ok := classifyPathInfo(hc, st, url)
		if !ok {
			printHuman(color.HiBlackString("    unreachable"))
			continue
		}
		if !v.accepts {
			printHuman(color.HiBlackString("    base %d, but a PathInfo tail -> 404: the extension is not script-mapped for PathInfo (or the handler rejects it). Not a PathInfo target.", v.baseStatus))
			continue
		}
		printHuman(color.HiBlackString("    base %d; PathInfo accepted (marker tail -> %d)", v.baseStatus, v.benignStatus))
		if v.mapsFile {
			printHuman(color.HiYellowString("    illegal-path-char oracle: benign %d, `|`/`\"` -> %d  => handler MAPS PathInfo to a filesystem path (MapPath/File.*)", v.benignStatus, v.illegalStatus))
		} else {
			printHuman(color.HiBlackString("    illegal-path-char oracle: no 5xx differential (benign %d, illegal %d)", v.benignStatus, v.illegalStatus))
		}
		if v.reflects {
			printHuman(color.HiYellowString("    reflection: PathInfo marker echoed in the 2xx body (handler uses it)"))
		}
		if v.physLeak {
			printHuman(color.HiYellowString("    physical-path leak: a drive-letter path (C:\\...) appears in a response (corroborates MapPath)"))
		}
		verify := color.HiBlackString("    verify (read-only): GET %s/web.config  (or a known file) — content that requestFiltering blocks on the direct path confirms it. This probe does NOT exfiltrate.", strings.TrimRight(url, "/"))
		switch v.confidence {
		case "confirmed":
			printHuman(color.New(color.FgHiRed, color.Bold).Sprintf("    [!! CONFIRMED] arbitrary FILE READ via PathInfo (CWE-22, application bug): %s", v.confirmEvid))
			printHuman(color.HiBlackString("    the handler served a file requestFiltering blocks on the direct path. Only a signature was captured, not the contents; this is the app's read, not an IIS bug."))
		case "high":
			printHuman(color.HiRedString("    [CANDIDATE: high] handler reads Request.PathInfo as a file path -> arbitrary-file-read candidate (CWE-22, an APPLICATION bug, not an IIS bug)."))
			printHuman(verify)
		case "medium":
			printHuman(color.HiYellowString("    [CANDIDATE: medium] handler is PathInfo-sensitive (5xx on a path-illegal char) but shows NO reflection/physical-path corroboration — it may map PathInfo to a file (CWE-22) OR just throw on those chars for another reason. Verify before trusting."))
			printHuman(verify)
		case "low":
			printHuman(color.HiYellowString("    [CANDIDATE: low] handler reflects PathInfo but shows no filesystem-read signal — check for path use / open-redirect / SSRF, and re-test manually (could be a soft-404 echo)."))
		default:
			printHuman(color.HiGreenString("    response is constant across PathInfo — handler does not appear to consume PathInfo."))
		}
	}
}

// pathInfoProbeAuto is the quiet --auto/--full hook: it runs only for resolved
// PathInfo-capable handler names and prints only a medium/high/confirmed result
// (silent for a clean handler, like the source-probe/desync auto convention).
// A confirmed hit also gets recorded for the end-of-scan recap — see
// runPathInfoSummary. Routed through ac.emitHuman so it lands in the right host
// block under --parallel.
func pathInfoProbeAuto(hc *http.Client, st *httpStats, ac *attackConfig, baseURL, name string) {
	if !hasPathInfoHandlerExt(name) {
		return
	}
	url := strings.TrimRight(baseURL, "/") + "/" + strings.TrimPrefix(name, "/")
	v, ok := classifyPathInfo(hc, st, url)
	if !ok || (v.confidence != "confirmed" && v.confidence != "high" && v.confidence != "medium") {
		return
	}
	if v.confirmed {
		recordPathInfoHit(ac, pathInfoHit{url: url, evidence: v.confirmEvid})
	}
	if args.Output == "human" {
		if v.confidence == "confirmed" {
			ac.emitHuman(fmt.Sprintf("  %s %s %s",
				color.New(color.FgHiRed, color.Bold).Sprint("[!! PathInfo FILE READ CONFIRMED]"),
				color.HiYellowString(url),
				color.HiBlackString("%s", v.confirmEvid)))
		} else {
			note := "reads Request.PathInfo as a file path (CWE-22 candidate)"
			if v.confidence == "medium" {
				note = "PathInfo-sensitive (5xx on a path-illegal char, no corroboration — may not be a file read)"
			}
			ac.emitHuman(fmt.Sprintf("  %s %s %s",
				color.HiRedString("[PathInfo read candidate: %s]", v.confidence),
				color.HiYellowString(url),
				color.HiBlackString("%s — verify: GET %s/web.config", note, url)))
		}
	} else {
		dt, tentative := "pathinfo-file-read-candidate", true
		if v.confidence == "confirmed" {
			dt, tentative = "pathinfo-file-read-confirmed", false
		}
		printJSON(resultOutput{
			Type: "pathinfo", Tentative: tentative, SourceDisclosure: v.confirmed, DisclosureType: dt,
			BaseUrl: baseURL, Fullname: name,
		})
	}
}

// pathInfoHit is one CONFIRMED PathInfo file-read, collected for the prominent
// end-of-scan summary so it is not lost in the middle of a long --auto run.
type pathInfoHit struct {
	url      string
	evidence string
}

// pathInfoHitStore accumulates confirmed PathInfo reads for one scan, per-scan
// (threaded via attackConfig, drained once after the directory loop) so a
// --parallel run never reports one host's finding under another host's block.
type pathInfoHitStore struct {
	mu   sync.Mutex
	hits []pathInfoHit
}

func recordPathInfoHit(ac *attackConfig, h pathInfoHit) {
	if ac == nil || ac.pathInfoHits == nil {
		return
	}
	ac.pathInfoHits.mu.Lock()
	ac.pathInfoHits.hits = append(ac.pathInfoHits.hits, h)
	ac.pathInfoHits.mu.Unlock()
}

func (s *pathInfoHitStore) drain() []pathInfoHit {
	s.mu.Lock()
	defer s.mu.Unlock()
	out := append([]pathInfoHit(nil), s.hits...)
	s.hits = nil
	return out
}

// runPathInfoSummary prints the prominent end-of-scan block for confirmed PathInfo
// file reads (human output only; JSON already emitted each finding inline).
func runPathInfoSummary(hits []pathInfoHit) {
	seen := map[string]bool{}
	var uniq []pathInfoHit
	for _, h := range hits {
		if !seen[h.url] {
			seen[h.url] = true
			uniq = append(uniq, h)
		}
	}
	if len(uniq) == 0 {
		return
	}
	// This recaps the SAME confirmed hit(s) already printed inline (as
	// "[!! PathInfo FILE READ CONFIRMED]") at the moment each was found — the
	// recap exists so a long --auto/--full run doesn't bury the finding, not to
	// report it as new. Say "recap" explicitly so a reader scanning the final
	// screen of output doesn't (mis)count this as additional distinct handlers.
	printHuman(color.New(color.FgHiRed, color.Bold).Sprintf("\n[!! PathInfo FILE READ - RECAP] %d confirmed handler(s) serving files via Request.PathInfo (CWE-22, application bug — not IIS; already reported inline above during the scan):", len(uniq)))
	for _, h := range uniq {
		printHuman(color.HiYellowString("    %s", h.url))
		printHuman(color.HiBlackString("       %s", h.evidence))
	}
}
