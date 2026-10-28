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
)

// fingerprint.go implements --fingerprint: a short, read-only probe matrix that
// classifies the target stack beyond the Server header and reports conservative
// routing/precondition signals for shortscan's disclosure modes. Three signals:
//
//  1. Version + substatus. When httpErrors errorMode=Detailed (common on dev /
//     staging / misconfigured hosts) the IIS error page leaks the exact version
//     and sc-substatus (404.8 hiddenSegment vs 404.11 double-escaping vs 404.0)
//     plus the module name — all in a body shortscan already downloads.
//  2. ADS / cookieless routing signals. Probing /bin vs /bin::$INDEX_ALLOCATION shows
//     whether the ::$INDEX_ALLOCATION form defeats requestFiltering (substatus
//     8 -> 0). It does not infer the content-read patch state without a known file.
//  3. Cross-stack. A non-IIS Server banner together with a working 8.3 oracle is
//     interesting but ambiguous: it may be a pure reverse proxy to IIS, or a shared
//     Windows file tier that resolves aliases. Only --retrieve's paired controls
//     establish the latter.
//
// It also surfaces advertised WebDAV capabilities (never exercised) and whether
// the allow-copy existence oracle
// (PROPFIND Depth:0 + COPY-in-Allow differential) is available here.

var (
	reIISDetailed = regexp.MustCompile(`(?i)IIS\s+([0-9]+\.[0-9]+)\s*-\s*([0-9]{3})\.([0-9]+)`)
	reIISModule   = regexp.MustCompile(`(?i)\b([A-Za-z]{4,}Module)\b`)
	reServerIIS   = regexp.MustCompile(`(?i)Microsoft-IIS/([0-9.]+)`)

	fingerprintMutex sync.Mutex
	// fingerprintDone records the strongest 8.3 result already printed for a
	// host. A recursive scan may see a non-vulnerable directory first and a
	// vulnerable one later; in that case the second pass must upgrade the report.
	fingerprintDone = map[string]bool{}
)

// schemeHost reduces a URL to scheme://host so --fingerprint runs once per host
// even when the scan recurses into many directories.
func schemeHost(raw string) string {
	u, err := nurl.Parse(raw)
	if err != nil || u.Host == "" {
		return strings.TrimRight(raw, "/")
	}
	return u.Scheme + "://" + u.Host
}

// fpRand returns a short path segment that is almost certainly not a real file.
func fpRand() string {
	return fmt.Sprintf("zz%dzz", rand.Intn(1<<30))
}

// substatusMeaning maps an IIS sc-substatus to a short human label.
func substatusMeaning(code string) string {
	switch code {
	case "404.0":
		return "not found"
	case "404.5", "404.6":
		return "URL/verb denied (requestFiltering)"
	case "404.7":
		return "file extension denied"
	case "404.8":
		return "hidden segment"
	case "404.11":
		return "double escaping"
	case "404.14":
		return "URL too long"
	case "403.14":
		return "directory listing denied"
	case "401.1", "401.2":
		return "auth required"
	case "403.4":
		return "SSL required"
	default:
		return ""
	}
}

// parseIISDetail extracts version, substatus and module hints from a detailed
// IIS error body. Empty strings when the page is a generic/custom error.
func parseIISDetail(body []byte) (version, substatus, module string) {
	s := string(body)
	if m := reIISDetailed.FindStringSubmatch(s); m != nil {
		version = m[1]
		substatus = m[2] + "." + m[3]
	}
	if m := reIISModule.FindStringSubmatch(s); m != nil {
		module = m[1]
	}
	return
}

// rePhysPath extracts the physical path IIS echoes in a detailed error page
// (post-canonicalization/collapse). Locale-independent: it matches the drive-letter
// path itself, not the "Caminho Físico"/"Physical Path" label around it.
var rePhysPath = regexp.MustCompile(`([A-Za-z]:\\[^<\r\n"]+)`)

func parsePhysicalPath(body []byte) string {
	if m := rePhysPath.FindStringSubmatch(string(body)); m != nil {
		return strings.TrimSpace(m[1])
	}
	return ""
}

// classifyCollapseMode detects whether the host runs the AGGRESSIVE cookieless
// path removal (unpatched, or aspnet:RestoreAggressiveCookielessPathRemoval=true —
// the CVE-2023-36899 / DuoDrop exposure) or the patched conservative default.
//
// It sends a two-token ext-split `/(S(1))/<a>/(S(1))<b>` and reads the post-collapse
// physical path from the detailed 404. Aggressive removal drops the leading token AND
// merges the embedded token's segment into the previous one, reuniting <a><b> with no
// token left in the path; the conservative patch removes only the leading token, so
// the embedded token survives in the physical path. That difference is a direct,
// source-free, read-only detector (validated on IIS 10 / .NET 4.8.1, both modes).
func classifyCollapseMode(hc *http.Client, st *httpStats, host string) (mode, phys string) {
	rnd := fpRand()
	a, b := "aq"+rnd, "wx"+rnd
	url := host + "/(S(1))/" + a + "/(S(1))" + b
	_, body, err := fetchBody(hc, st, "GET", url, 1<<15)
	if err != nil {
		return "", ""
	}
	phys = parsePhysicalPath(body)
	if phys == "" {
		return "", "" // detailed errors off — undetectable this way
	}
	// The token count in the collapsed physical path tells the three modes apart:
	//   0 tokens + <a><b> reunited → aggressive (leading + embedded both removed)
	//   1 token  (embedded survives, leading gone) → patched ASP.NET cookieless
	//   2 tokens (leading survives too, nothing removed) → the host does no
	//     cookieless path removal at all (non-ASP.NET, or cookieless disabled) —
	//     NOT "patched", just not applicable. (<a>/<b> never contain "(s(".)
	low := strings.ToLower(phys)
	tokens := strings.Count(low, "(s(")
	switch {
	case tokens == 0 && strings.Contains(low, strings.ToLower(a+b)):
		return "AGGRESSIVE — CVE-2023-36899 cookieless collapse EXPOSED (web.config→machineKey→RCE reachable via ext-split; run --source-probe)", phys
	case tokens == 1:
		return "conservative (patched — aggressive cookieless removal OFF)", phys
	case tokens >= 2:
		return "n/a — host does no cookieless path removal (non-ASP.NET or cookieless disabled)", phys
	default:
		return "inconclusive (physical path matched no known collapse shape)", phys
	}
}

// fingerprintProbe fetches a URL and returns status plus parsed detail. A nil
// response (transport error) yields status 0.
func fingerprintProbe(hc *http.Client, st *httpStats, method, url string) (status int, version, substatus, module string, res *http.Response) {
	r, body, err := fetchBody(hc, st, method, url, 1<<15)
	if err != nil || r == nil {
		return 0, "", "", "", nil
	}
	version, substatus, module = parseIISDetail(body)
	return r.StatusCode, version, substatus, module, r
}

// singleStackHosts records hosts the fingerprint classified as single-stack IIS
// (an IIS banner + working 8.3 oracle, no non-IIS front-end). --retrieve reads the
// alias on a NON-IIS tier, so against such a host on the same origin it only ever
// gets IIS's own 404.0 — the retrieve step skips it unless --retrieve-base points
// at a real non-IIS tier. This is retrieve's documented premise, not a patch guess.
var (
	singleStackMu    sync.Mutex
	singleStackHosts = map[string]bool{}
)

func markSingleStackIIS(host string) {
	singleStackMu.Lock()
	singleStackHosts[host] = true
	singleStackMu.Unlock()
}

func isSingleStackIIS(host string) bool {
	singleStackMu.Lock()
	defer singleStackMu.Unlock()
	return singleStackHosts[host]
}

// runFingerprint runs the probe matrix once per host and prints the block.
func runFingerprint(url string, hc *http.Client, st *httpStats, tildeOracle bool, srv string, nonIISBanner bool) {
	host := schemeHost(url)

	fingerprintMutex.Lock()
	previousTilde, done := fingerprintDone[host]
	if done && (previousTilde || !tildeOracle) {
		fingerprintMutex.Unlock()
		return
	}
	fingerprintDone[host] = tildeOracle
	fingerprintMutex.Unlock()

	out := fingerprintOutput{Type: "fingerprint", Url: host, Server: srv, TildeOracle: tildeOracle}

	// The fingerprint's ~8 probes are mutually independent, so fire them
	// concurrently and classify once they all return. It runs once per host and
	// --auto now enables it, so paying ~8 sequential round-trips before the scan
	// proceeds would re-add the startup latency the concurrent char-discovery
	// otherwise removed. Each goroutine writes a distinct variable — no lock.
	rnd := fpRand()
	var (
		hdrRes                     *http.Response
		optRes                     *http.Response
		optErr                     error
		allowCopyMatched           bool
		hiddenStatus, adsStatus    int
		plainStatus, cookieStatus  int
		ver1, subHidden, modHidden string
		ver2, subCfg, modCfg       string
		subADS, modADS             string
		collapseMode, collapsePhys string
	)
	var wg sync.WaitGroup
	launch := func(f func()) { wg.Add(1); go func() { defer wg.Done(); f() }() }
	launch(func() { _, _, _, _, hdrRes = fingerprintProbe(hc, st, "GET", host+"/") })
	launch(func() {
		hiddenStatus, ver1, subHidden, modHidden, _ = fingerprintProbe(hc, st, "GET", host+"/bin/"+rnd+".htm")
	})
	launch(func() { _, ver2, subCfg, modCfg, _ = fingerprintProbe(hc, st, "GET", host+"/web.config") })
	launch(func() {
		adsStatus, _, subADS, modADS, _ = fingerprintProbe(hc, st, "GET", host+"/bin::$INDEX_ALLOCATION/"+rnd+".htm")
	})
	launch(func() { plainStatus, _, _, _, _ = fingerprintProbe(hc, st, "GET", host+"/"+rnd+".htm") })
	launch(func() { cookieStatus, _, _, _, _ = fingerprintProbe(hc, st, "GET", host+"/(S("+rnd+"))/"+rnd+".htm") })
	launch(func() { collapseMode, collapsePhys = classifyCollapseMode(hc, st, host) })
	launch(func() { optRes, optErr = fetch(hc, st, "OPTIONS", host+"/") })
	launch(func() {
		_, allowCopyMatched, _ = allowCopyExistsAgainstBaseline(hc, st, host+"/", "web.config", "", ".config")
	})
	wg.Wait()

	// Header pass: X-Powered-By / MVC / ASP.NET / Server.
	if hdrRes != nil {
		out.PoweredBy = strings.TrimSpace(hdrRes.Header.Get("X-Powered-By"))
		out.AspNet = strings.TrimSpace(hdrRes.Header.Get("X-AspNet-Version"))
		out.AspNetMvc = strings.TrimSpace(hdrRes.Header.Get("X-AspNetMvc-Version"))
		if m := reServerIIS.FindStringSubmatch(hdrRes.Header.Get("Server")); m != nil {
			out.IISVersion = m[1]
		}
	}

	// --- Item 1: version + substatus via detailed errors ---
	// /bin/<rnd> is a hiddenSegment control; /web.config is a denied-file control.
	addSub := func(sub, mod, where string) {
		if sub == "" {
			return
		}
		out.DetailedErrors = true
		label := sub
		if meaning := substatusMeaning(sub); meaning != "" {
			label += " " + meaning
		}
		if mod != "" {
			label += " [" + mod + "]"
		}
		label += " (" + where + ")"
		out.Substatuses = append(out.Substatuses, label)
	}
	addSub(subHidden, modHidden, "/bin/*")
	addSub(subCfg, modCfg, "/web.config")
	addSub(subADS, modADS, "/bin::$INDEX_ALLOCATION/*")
	for _, v := range []string{ver1, ver2} {
		if v != "" && out.IISVersion == "" {
			out.IISVersion = v
		}
	}

	// --- Item 2: ADS / cookieless routing signals ---
	switch {
	case subHidden == "404.8" && subADS == "404.0":
		out.ADSFilterBypass = "LIVE — ::$INDEX_ALLOCATION changes hiddenSegment 404.8 to ordinary 404.0. This confirms namespace reachability, not content read."
		out.Notes = append(out.Notes, "ADS/index namespace reached past the URL-string hiddenSegment check; content-read gating still requires a known-file probe.")
	case subHidden == "404.8" && subADS == "404.8":
		out.ADSFilterBypass = "blocked — the stream form is still caught as a hidden segment."
	case hiddenStatus != 0 && adsStatus != 0 && !out.DetailedErrors:
		out.ADSFilterBypass = fmt.Sprintf("inconclusive (detailed errors off): /bin=%d /bin::$INDEX_ALLOCATION=%d", hiddenStatus, adsStatus)
	default:
		out.ADSFilterBypass = "inconclusive"
	}

	// Cookieless token acceptance: compare a plain miss to a token-wrapped miss.
	switch {
	case cookieStatus == 0:
		out.Cookieless = "no response"
	case cookieStatus == plainStatus:
		out.Cookieless = fmt.Sprintf("same miss status (%d) — inconclusive without a known existing path", cookieStatus)
	default:
		out.Cookieless = fmt.Sprintf("plain=%d token=%d — token segment changes routing", plainStatus, cookieStatus)
	}

	// Collapse mode: the CVE-2023-36899 exposure detector (white-box via the
	// detailed-error physical path). Only set when detailed errors disclosed a path.
	out.CollapseMode = collapseMode
	out.PhysicalPath = collapsePhys

	// --- Item 3: cross-stack verdict ---
	isIIS := out.IISVersion != "" || strings.Contains(strings.ToUpper(srv), "IIS")
	switch {
	case tildeOracle && !isIIS:
		out.CrossStack = "interesting — non-IIS banner + working 8.3 oracle may be a reverse proxy to IIS OR a shared Windows file tier. No read claim; --retrieve uses paired controls."
	case tildeOracle && nonIISBanner:
		out.CrossStack = "mixed banner — may be a proxy chain or shared file tier. No read claim; verify with --retrieve."
	case tildeOracle && isIIS:
		out.CrossStack = "single-stack IIS — enumeration works; --retrieve reads the alias on a non-IIS tier, so --auto skips it same-origin here (pass --retrieve-base <non-IIS origin> to force a cross-stack read)."
		markSingleStackIIS(host)
	default:
		out.CrossStack = "n/a (no 8.3 oracle on this host)"
	}

	// WebDAV capabilities (flagged, never exercised).
	if optErr == nil && optRes != nil {
		dav := strings.TrimSpace(optRes.Header.Get("DAV"))
		allow := strings.ToUpper(optRes.Header.Get("Allow"))
		if dav != "" || strings.Contains(allow, "PROPFIND") {
			methods, _ := normaliseAllow(allow, false)
			methodSet := "," + methods + ","
			writes := []string{}
			for _, m := range []string{"PUT", "DELETE", "COPY", "MOVE", "MKCOL", "LOCK"} {
				if strings.Contains(methodSet, ","+m+",") {
					writes = append(writes, m)
				}
			}
			line := "enabled (DAV: " + dav + ")"
			if len(writes) > 0 {
				line += " — mutating methods advertised: " + strings.Join(writes, ",") + " [authorization unverified; not exercised]"
				out.Notes = append(out.Notes, "Advertised WebDAV methods do not prove write/delete authorization. If usable, they act with the configured IIS identity and are not OS local privilege escalation.")
			}
			out.WebDAV = line
		} else {
			out.WebDAV = "not advertised"
		}
	}
	// allow-copy oracle availability (paired positive/negative, prefetched above).
	if allowCopyMatched {
		out.AllowCopyOracle = true
	}

	if bulkCompact() {
		// Bulk-compact: stash it so the per-host header prints it as one line
		// instead of the full block (see the URL block in Scan).
		setHostFingerprint(out)
	} else {
		printFingerprintHuman(out)
	}
	printJSON(out)
}

// fingerprintCompactLine renders the fingerprint as a single dim line for the
// bulk-compact per-host block, e.g.
// "IIS 10.0 · ASP.NET 4.0.30319 · 8.3:yes · single-stack · DAV:no".
func fingerprintCompactLine(o fingerprintOutput) string {
	yesno := func(b bool) string {
		if b {
			return "yes"
		}
		return "no"
	}
	// o.Server may carry a trailing suspicious-banner marker (" [!]") added in
	// Scan; the compact header re-expresses it on the verdict, so drop it here.
	// TrimSuffix reuses the exact formatter that appended it, so it matches
	// whether colour is on or off.
	server := strings.TrimSpace(strings.TrimSuffix(o.Server, " "+color.HiRedString("[!]")))
	parts := []string{}
	switch {
	case o.IISVersion != "":
		parts = append(parts, "IIS "+o.IISVersion)
	case server != "":
		parts = append(parts, server)
	default:
		parts = append(parts, "<unknown>")
	}
	if o.AspNet != "" {
		parts = append(parts, "ASP.NET "+o.AspNet)
	} else if strings.Contains(strings.ToUpper(o.PoweredBy), "ASP.NET") {
		parts = append(parts, "ASP.NET")
	}
	parts = append(parts, "8.3:"+yesno(o.TildeOracle))
	switch {
	case strings.HasPrefix(o.CrossStack, "single-stack"):
		parts = append(parts, "single-stack")
	case strings.HasPrefix(o.CrossStack, "interesting"), strings.HasPrefix(o.CrossStack, "mixed"):
		parts = append(parts, "cross-stack?")
	}
	switch {
	case strings.HasPrefix(o.WebDAV, "enabled"):
		parts = append(parts, "DAV:yes")
	case o.WebDAV == "not advertised":
		parts = append(parts, "DAV:not advertised")
	}
	if o.AllowCopyOracle {
		parts = append(parts, "allow-copy")
	}
	if len(o.Substatuses) > 0 {
		parts = append(parts, "errors:on")
	}
	return strings.Join(parts, " · ")
}

// printFingerprintHuman renders the fingerprint block.
func printFingerprintHuman(o fingerprintOutput) {
	if args.Output != "human" {
		return
	}
	if args.Verbosity == 0 {
		printFingerprintSummary(o)
		return
	}
	bold := color.New(color.FgWhite, color.Bold).Sprint
	lbl := func(s string) string { return color.New(color.FgWhite, color.Bold).Sprintf("  %-13s", s) }

	printHuman()
	printHuman(bold("Fingerprint") + ": " + o.Url)
	server := o.Server
	if o.IISVersion != "" {
		server += "  " + color.HiBlackString("(IIS "+o.IISVersion+")")
	}
	printHuman(lbl("Server"), server)
	if o.PoweredBy != "" || o.AspNet != "" || o.AspNetMvc != "" {
		bits := []string{}
		if o.AspNet != "" {
			bits = append(bits, "ASP.NET "+o.AspNet)
		}
		if o.AspNetMvc != "" {
			bits = append(bits, "MVC "+o.AspNetMvc)
		}
		if o.PoweredBy != "" {
			bits = append(bits, "X-Powered-By: "+o.PoweredBy)
		}
		printHuman(lbl("Framework"), strings.Join(bits, "  "))
	}
	if o.DetailedErrors {
		printHuman(lbl("Substatus"), color.HiYellowString(strings.Join(o.Substatuses, "   ")))
	} else {
		printHuman(lbl("Substatus"), color.HiBlackString("detailed errors OFF — substatus not disclosed remotely"))
	}
	oracle := color.HiRedString("no")
	if o.TildeOracle {
		oracle = color.HiGreenString("yes")
	}
	printHuman(lbl("8.3 oracle"), oracle)

	cross := o.CrossStack
	switch {
	case strings.HasPrefix(cross, "interesting"), strings.HasPrefix(cross, "mixed"):
		cross = color.HiYellowString(cross)
	default:
		cross = color.HiBlackString(cross)
	}
	printHuman(lbl("Cross-stack"), cross)

	ads := o.ADSFilterBypass
	if strings.HasPrefix(ads, "LIVE") {
		ads = color.HiGreenString(ads)
	} else {
		ads = color.HiBlackString(ads)
	}
	printHuman(lbl("ADS/filter"), ads)
	printHuman(lbl("Cookieless"), color.HiBlackString(o.Cookieless))
	if o.CollapseMode != "" {
		cm := o.CollapseMode
		if strings.HasPrefix(cm, "AGGRESSIVE") {
			cm = color.HiRedString(cm)
		} else {
			cm = color.HiBlackString(cm)
		}
		line := cm
		if o.PhysicalPath != "" {
			line += color.HiBlackString("  [phys: %s]", o.PhysicalPath)
		}
		printHuman(lbl("Collapse"), line)
	}
	if o.WebDAV != "" {
		wd := o.WebDAV
		if strings.Contains(wd, "mutating methods") {
			wd = color.HiYellowString(wd)
		} else {
			wd = color.HiBlackString(wd)
		}
		allowCopy := ""
		if o.AllowCopyOracle {
			allowCopy = color.HiCyanString("  · allow-copy oracle available (--brute-oracle allow-copy)")
		}
		printHuman(lbl("WebDAV"), wd+allowCopy)
	}
	for _, n := range o.Notes {
		printHuman("  " + color.HiBlackString("· "+n))
	}
}
