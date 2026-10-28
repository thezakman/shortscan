package shortscan

import (
	"fmt"
	stdhtml "html"
	"net/http"
	nurl "net/url"
	"path"
	"regexp"
	"sort"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
	"github.com/thezakman/shortscan/pkg/shortutil"
)

const (
	maxReferenceNamesPerOrigin = 4096
	maxReferencesPerPage       = 256
)

type referenceEvidence struct {
	record wordlistRecord
	source string
	target string
}

// referenceKnowledge is a target-specific wordlist built from public paths
// found in same-origin HTML, JavaScript and CSS. Every derived long name still
// has to pass the configured HTTP oracle before it is reported as recovered.
type referenceKnowledge struct {
	sync.RWMutex
	byOrigin map[string]map[string]referenceEvidence
}

type referenceCrawlStats struct {
	pages      int
	references int
	names      int
	bytes      int
	errors     int
}

type referenceCrawlItem struct {
	url    string
	depth  int
	source string
}

type referenceRecordCandidate struct {
	record       wordlistRecord
	directType   string
	checksumType string
}

type referenceCrawler struct {
	sync.Mutex
	knowledge *referenceKnowledge
	seen      map[string]struct{}
	pages     int
	maxPages  int
	maxDepth  int
	bodyLimit int64
}

var (
	htmlReferencePattern = regexp.MustCompile("(?is)\\b(?:src|href)\\s*=\\s*(?:\"([^\"]+)\"|'([^']+)'|([^\\s\"'<>]+))")
	cssReferencePattern  = regexp.MustCompile("(?is)url\\(\\s*(?:\"([^\"]+)\"|'([^']+)'|([^\\s)'\"]+))\\s*\\)")
	quotedStringPattern  = regexp.MustCompile("[\"'`]([^\"'`\\r\\n]{1,512})[\"'`]")
)

var referenceLikeExtensions = map[string]struct{}{
	".asp": {}, ".aspx": {}, ".asax": {}, ".ascx": {}, ".asmx": {}, ".ashx": {}, ".axd": {},
	".config": {}, ".css": {}, ".cshtml": {}, ".htm": {}, ".html": {}, ".js": {}, ".json": {},
	".map": {}, ".master": {}, ".mjs": {}, ".razor": {}, ".svc": {}, ".txt": {}, ".vbhtml": {},
	".wasm": {}, ".webmanifest": {}, ".svg": {}, ".woff": {}, ".woff2": {}, ".ttf": {}, ".otf": {},
	".br": {}, ".gz": {}, ".wsdl": {}, ".xml": {}, ".xsd": {},
}

var crawlableReferenceExtensions = map[string]struct{}{
	".asp": {}, ".aspx": {}, ".ascx": {}, ".asmx": {}, ".ashx": {}, ".css": {}, ".cshtml": {},
	".htm": {}, ".html": {}, ".js": {}, ".json": {}, ".map": {}, ".mjs": {}, ".razor": {},
	".svc": {}, ".vbhtml": {}, ".xml": {},
}

func newReferenceKnowledge() *referenceKnowledge {
	return &referenceKnowledge{byOrigin: make(map[string]map[string]referenceEvidence)}
}

func newReferenceCrawler(knowledge *referenceKnowledge, maxPages, maxDepth, bodyLimit int) *referenceCrawler {
	if maxPages <= 0 {
		maxPages = 24
	}
	if maxDepth < 0 {
		maxDepth = 0
	}
	if bodyLimit <= 0 {
		bodyLimit = 262144
	}
	return &referenceCrawler{
		knowledge: knowledge,
		seen:      make(map[string]struct{}),
		maxPages:  maxPages,
		maxDepth:  maxDepth,
		bodyLimit: int64(bodyLimit),
	}
}

func needsConfiguredWordlist(autocomplete string) bool {
	return !args.ReferenceOnly && (autocomplete != "none" || args.ProbeCandidates || candidateOutputWriter != nil)
}

func sanitisedReferenceSource(rawURL string) string {
	u, err := nurl.Parse(rawURL)
	if err != nil {
		return rawURL
	}
	u.User = nil
	u.RawQuery = ""
	u.Fragment = ""
	return u.String()
}

// referenceChecksums mirrors the case variants accepted by rainbow tables and
// also includes the Windows Server 2003/XP checksum. Public references retain
// their original case, but links are frequently emitted with different casing
// from the on-disk NTFS name. Every checksum match remains only a candidate and
// must pass the configured HTTP oracle before it is reported.
func referenceChecksums(longName string) string {
	variants := []string{
		longName,
		strings.ToLower(longName),
		strings.ToUpper(longName),
		strings.Title(longName), //nolint:staticcheck // parity with shortutil wordlist variants
	}
	checksums := ""
	for _, variant := range variants {
		checksums = mergeChecksums(checksums, shortutil.Checksum(variant))
		if len(variant) >= 2 {
			checksums = mergeChecksums(checksums, shortutil.ChecksumOriginal(variant))
		}
	}
	return checksums
}

func recordHasChecksum(record wordlistRecord, checksum string) bool {
	for offset := 0; offset+4 <= len(record.checksums); offset += 4 {
		if strings.EqualFold(record.checksums[offset:offset+4], checksum) {
			return true
		}
	}
	return false
}

func compressedCompanionRecord(record wordlistRecord, shortExtension string) (wordlistRecord, bool) {
	compressedExtension := "." + strings.ToLower(shortExtension)
	if shortExtension != "BR" && shortExtension != "GZ" {
		return wordlistRecord{}, false
	}
	if record.filename == "" || record.extension == "" ||
		strings.EqualFold(record.extension, compressedExtension) {
		return wordlistRecord{}, false
	}
	// Precompressed web assets retain the original extension in the basename:
	// service-worker.js -> service-worker.js.br. Windows then treats only .br
	// as the extension when it builds the 8.3 alias.
	filename := record.filename + record.extension
	_, filename83, extension83 := shortutil.Gen8dot3(filename, compressedExtension)
	return wordlistRecord{
		checksums: referenceChecksums(filename + compressedExtension),
		filename:  filename, extension: compressedExtension,
		filename83: filename83, extension83: extension83,
	}, true
}

// rememberURL decomposes a referenced path into directory and filename
// components, then precomputes the same approximate 8.3 fields used by the
// normal wordlist. Query strings and fragments never become candidate names.
func (knowledge *referenceKnowledge) rememberURL(rawURL, source string) int {
	if knowledge == nil {
		return 0
	}
	u, err := nurl.Parse(rawURL)
	if err != nil {
		return 0
	}
	origin := originKey(rawURL)
	if origin == "" {
		return 0
	}
	decodedPath, err := nurl.PathUnescape(u.EscapedPath())
	if err != nil {
		decodedPath = u.Path
	}
	segments := strings.Split(strings.Trim(decodedPath, "/"), "/")
	added := 0
	knowledge.Lock()
	defer knowledge.Unlock()
	if knowledge.byOrigin == nil {
		knowledge.byOrigin = make(map[string]map[string]referenceEvidence)
	}
	if knowledge.byOrigin[origin] == nil {
		knowledge.byOrigin[origin] = make(map[string]referenceEvidence)
	}
	records := knowledge.byOrigin[origin]
	for _, segment := range segments {
		segment = strings.TrimSpace(stdhtml.UnescapeString(segment))
		if segment == "" || segment == "." || segment == ".." || strings.ContainsAny(segment, "\\:*?\"<>|") {
			continue
		}
		extension := path.Ext(segment)
		filename := strings.TrimSuffix(segment, extension)
		if filename == "" {
			continue
		}
		_, filename83, extension83 := shortutil.Gen8dot3(filename, extension)
		if filename83 == "" {
			continue
		}
		key := strings.ToLower(filename + "\x00" + extension)
		if _, exists := records[key]; exists || len(records) >= maxReferenceNamesPerOrigin {
			continue
		}
		records[key] = referenceEvidence{
			record: wordlistRecord{
				checksums: referenceChecksums(filename + extension),
				filename:  filename, extension: extension,
				filename83: filename83, extension83: extension83,
			},
			source: sanitisedReferenceSource(source),
			target: sanitisedReferenceSource(rawURL),
		}
		added++
	}
	return added
}

func (knowledge *referenceKnowledge) recordsFor(rawURL string) []referenceEvidence {
	if knowledge == nil {
		return nil
	}
	origin := originKey(rawURL)
	knowledge.RLock()
	records := knowledge.byOrigin[origin]
	result := make([]referenceEvidence, 0, len(records))
	for _, record := range records {
		result = append(result, record)
	}
	knowledge.RUnlock()
	sort.Slice(result, func(i, j int) bool {
		left := strings.ToLower(result[i].record.filename + result[i].record.extension)
		right := strings.ToLower(result[j].record.filename + result[j].record.extension)
		return left < right
	})
	return result
}

func referenceFilenameCandidates(ac *attackConfig, br baseRequest) []filenameCandidate {
	if !args.CrawlReferences || ac == nil || ac.references == nil || br.file == "" {
		return nil
	}
	shortExtension := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
	upperFile := strings.ToUpper(br.file)
	checksumPrefix, checksum := "", ""
	if checksumRegex != nil && checksumRegex.MatchString(upperFile) && len(upperFile) >= 5 {
		checksumPrefix, checksum = upperFile[:len(upperFile)-4], upperFile[len(upperFile)-4:]
	}
	var result []filenameCandidate
	for _, evidence := range ac.references.recordsFor(br.url) {
		records := []referenceRecordCandidate{{evidence.record, "reference", "reference-checksum"}}
		if companion, ok := compressedCompanionRecord(evidence.record, shortExtension); ok {
			records = append(records, referenceRecordCandidate{companion, "reference-compressed", "reference-compressed-checksum"})
		}
		for _, candidate := range records {
			matchType := ""
			if strings.EqualFold(candidate.record.filename83, br.file) &&
				strings.EqualFold(candidate.record.extension83, shortExtension) {
				matchType = candidate.directType
			} else if checksum != "" &&
				strings.HasPrefix(strings.ToUpper(candidate.record.filename), checksumPrefix) &&
				strings.EqualFold(candidate.record.extension83, shortExtension) &&
				recordHasChecksum(candidate.record, checksum) {
				matchType = candidate.checksumType
			}
			if matchType == "" {
				continue
			}
			result = append(result, filenameCandidate{
				record:    candidate.record,
				matchType: matchType,
				source:    evidence.source,
			})
		}
	}
	return result
}

func referenceValue(match []string) string {
	for _, value := range match[1:] {
		if value != "" {
			return value
		}
	}
	return ""
}

func looksLikeQuotedReference(value string) bool {
	value = strings.TrimSpace(strings.ToLower(value))
	if value == "" || strings.Contains(value, "${") || strings.Contains(value, "{{") || strings.Contains(value, "<%") {
		return false
	}
	if strings.HasPrefix(value, "/") || strings.HasPrefix(value, "./") || strings.HasPrefix(value, "../") ||
		strings.HasPrefix(value, "http://") || strings.HasPrefix(value, "https://") || strings.Contains(value, "/") {
		return true
	}
	_, exists := referenceLikeExtensions[strings.ToLower(path.Ext(value))]
	return exists
}

func extractReferenceValues(body []byte) []string {
	text := string(body)
	seen := make(map[string]struct{})
	result := make([]string, 0)
	add := func(value string, requirePathShape bool) {
		value = strings.TrimSpace(stdhtml.UnescapeString(value))
		value = strings.ReplaceAll(value, `\/`, "/")
		value = strings.ReplaceAll(value, `\u002f`, "/")
		value = strings.ReplaceAll(value, `\u002F`, "/")
		if value == "" || len(value) > 1024 || (requirePathShape && !looksLikeQuotedReference(value)) {
			return
		}
		key := strings.ToLower(value)
		if _, exists := seen[key]; exists || len(result) >= maxReferencesPerPage {
			return
		}
		seen[key] = struct{}{}
		result = append(result, value)
	}
	for _, match := range htmlReferencePattern.FindAllStringSubmatch(text, -1) {
		add(referenceValue(match), false)
	}
	for _, match := range cssReferencePattern.FindAllStringSubmatch(text, -1) {
		add(referenceValue(match), false)
	}
	for _, match := range quotedStringPattern.FindAllStringSubmatch(text, -1) {
		add(referenceValue(match), true)
	}
	return result
}

func resolveSameOriginReference(baseURL, value, expectedOrigin string) (string, bool) {
	value = strings.TrimSpace(stdhtml.UnescapeString(value))
	if value == "" || strings.HasPrefix(value, "#") {
		return "", false
	}
	lower := strings.ToLower(value)
	for _, prefix := range []string{"javascript:", "data:", "mailto:", "tel:", "blob:"} {
		if strings.HasPrefix(lower, prefix) {
			return "", false
		}
	}
	base, err := nurl.Parse(baseURL)
	if err != nil {
		return "", false
	}
	reference, err := nurl.Parse(value)
	if err != nil {
		return "", false
	}
	resolved := base.ResolveReference(reference)
	resolved.Fragment = ""
	resolved.User = nil
	if resolved.Scheme != "http" && resolved.Scheme != "https" {
		return "", false
	}
	if originKey(resolved.String()) != expectedOrigin {
		return "", false
	}
	return resolved.String(), true
}

func crawlableReference(rawURL string) bool {
	u, err := nurl.Parse(rawURL)
	if err != nil {
		return false
	}
	if strings.HasSuffix(u.Path, "/") {
		return true
	}
	if path.Ext(u.Path) == "" {
		// Keep extensionless references as candidate names, but do not follow
		// them automatically. An operator can make one an explicit seed when it
		// is known to be a read-only page.
		return false
	}
	_, exists := crawlableReferenceExtensions[strings.ToLower(path.Ext(u.Path))]
	return exists
}

func referenceContent(rawURL string, header http.Header) bool {
	contentType := strings.ToLower(header.Get("Content-Type"))
	for _, marker := range []string{"text/html", "application/xhtml", "javascript", "ecmascript", "text/css", "application/json", "text/json", "text/xml", "application/xml"} {
		if strings.Contains(contentType, marker) {
			return true
		}
	}
	if contentType != "" && !strings.Contains(contentType, "text/plain") {
		return false
	}
	return crawlableReference(rawURL)
}

func (crawler *referenceCrawler) reserve(rawURL string) bool {
	crawler.Lock()
	defer crawler.Unlock()
	if crawler.pages >= crawler.maxPages {
		return false
	}
	if _, exists := crawler.seen[rawURL]; exists {
		return false
	}
	crawler.seen[rawURL] = struct{}{}
	crawler.pages++
	return true
}

// crawl performs bounded breadth-first GETs. It never follows cross-origin
// references, never submits forms, and reads at most bodyLimit bytes per page.
func (crawler *referenceCrawler) crawl(hc *http.Client, st *httpStats, baseURL string, seeds []string) referenceCrawlStats {
	var stats referenceCrawlStats
	if crawler == nil || crawler.knowledge == nil || hc == nil {
		return stats
	}
	expectedOrigin := originKey(baseURL)
	if expectedOrigin == "" {
		return stats
	}
	queue := make([]referenceCrawlItem, 0, len(seeds))
	for _, seed := range seeds {
		resolved, ok := resolveSameOriginReference(baseURL, seed, expectedOrigin)
		if ok {
			queue = append(queue, referenceCrawlItem{url: resolved, source: baseURL})
		}
	}
	for len(queue) > 0 {
		item := queue[0]
		queue = queue[1:]
		if !crawler.reserve(item.url) {
			continue
		}
		stats.pages++
		stats.names += crawler.knowledge.rememberURL(item.url, item.source)
		res, body, err := fetchBody(hc, st, http.MethodGet, item.url, crawler.bodyLimit)
		if err != nil {
			stats.errors++
			continue
		}
		stats.bytes += len(body)
		if res.StatusCode >= 300 && res.StatusCode < 400 {
			if location := res.Header.Get("Location"); location != "" && item.depth <= crawler.maxDepth {
				if resolved, ok := resolveSameOriginReference(item.url, location, expectedOrigin); ok {
					queue = append(queue, referenceCrawlItem{url: resolved, depth: item.depth, source: item.url})
				}
			}
			continue
		}
		if res.StatusCode < 200 || res.StatusCode >= 300 || !referenceContent(item.url, res.Header) {
			continue
		}
		for _, value := range extractReferenceValues(body) {
			resolved, ok := resolveSameOriginReference(item.url, value, expectedOrigin)
			if !ok {
				continue
			}
			stats.references++
			stats.names += crawler.knowledge.rememberURL(resolved, item.url)
			if item.depth < crawler.maxDepth && crawlableReference(resolved) {
				queue = append(queue, referenceCrawlItem{url: resolved, depth: item.depth + 1, source: item.url})
			}
		}
	}
	return stats
}

func mergeReferenceCrawlStats(left, right referenceCrawlStats) referenceCrawlStats {
	return referenceCrawlStats{
		pages: left.pages + right.pages, references: left.references + right.references,
		names: left.names + right.names, bytes: left.bytes + right.bytes, errors: left.errors + right.errors,
	}
}

// reportReferenceCrawl prints one crawl phase's totals. label distinguishes the
// two phases in Scan() — "initial" (the directory's own page(s), crawled up
// front) from "follow-up" (pages that only became reachable once the 8.3
// enumeration itself resolved their long name) — since otherwise the two
// printed lines are indistinguishable and read as the same crawl repeating.
func reportReferenceCrawl(ac *attackConfig, stats referenceCrawlStats, label string) {
	if stats.pages == 0 && stats.names == 0 {
		return
	}
	if bulkCompact() && stats.names == 0 {
		// No recovered names — pure crawl bookkeeping, noise in the compact view.
		return
	}
	beginSection(ac)
	parts := []string{
		pluralCount(stats.pages, "page", "pages"),
		pluralCount(stats.references, "ref", "refs"),
		pluralCount(stats.names, "name", "names"),
		formatBytes(stats.bytes),
	}
	if stats.errors > 0 {
		parts = append(parts, pluralCount(stats.errors, "error", "errors"))
	}
	printHuman(color.HiCyanString("[REF-CRAWL:%s]", label) + " " + strings.Join(parts, " · "))
	printJSON(map[string]any{
		"type": "reference-statistics", "phase": label, "pages": stats.pages, "references": stats.references,
		"names": stats.names, "bytes": stats.bytes, "errors": stats.errors,
	})
}

func rememberReferenceSeed(ac *attackConfig, baseURL, candidatePath string) {
	if !args.CrawlReferences || ac == nil {
		return
	}
	rawURL := baseURL + candidatePath
	if !crawlableReference(rawURL) {
		return
	}
	ac.referenceMutex.Lock()
	if ac.referenceSeeds == nil {
		ac.referenceSeeds = make(map[string]struct{})
	}
	ac.referenceSeeds[rawURL] = struct{}{}
	ac.referenceMutex.Unlock()
}

func takeReferenceSeeds(ac *attackConfig) []string {
	if ac == nil {
		return nil
	}
	ac.referenceMutex.Lock()
	seeds := make([]string, 0, len(ac.referenceSeeds))
	for seed := range ac.referenceSeeds {
		seeds = append(seeds, seed)
		delete(ac.referenceSeeds, seed)
	}
	ac.referenceMutex.Unlock()
	sort.Strings(seeds)
	return seeds
}

func observeRecoveryAlias(ac *attackConfig, br baseRequest) {
	// recoverStemBruteAliases (stembrute.go) reads ac.observedAliases too, so --brute
	// must keep this observation running even when run standalone (without
	// --sibling-recovery/--crawl-references/--collision-ancestry) — otherwise it
	// silently recovers nothing, having never seen a single alias to brute from.
	if (!args.SiblingRecovery && !args.CrawlReferences && !args.CollisionAncestry && !args.Brute) || ac == nil {
		return
	}
	key := strings.ToLower(br.url + "\x00" + br.file + "\x00" + br.ext)
	ac.autocompleteMutex.Lock()
	if ac.observedAliases == nil {
		ac.observedAliases = make(map[string]baseRequest)
	}
	if _, exists := ac.observedAliases[key]; !exists {
		ac.observedAliases[key] = br
	}
	ac.autocompleteMutex.Unlock()
}

func observedRecoveryAliases(ac *attackConfig) []baseRequest {
	if ac == nil {
		return nil
	}
	ac.autocompleteMutex.Lock()
	aliases := make([]baseRequest, 0, len(ac.observedAliases))
	for _, br := range ac.observedAliases {
		aliases = append(aliases, br)
	}
	ac.autocompleteMutex.Unlock()
	sort.Slice(aliases, func(i, j int) bool {
		left := strings.ToLower(aliases[i].url + aliases[i].file + aliases[i].ext)
		right := strings.ToLower(aliases[j].url + aliases[j].file + aliases[j].ext)
		return left < right
	})
	return aliases
}

// recoverReferenceAliases is a deterministic post-crawl pass for aliases that
// were enumerated before a later HTML/JS page revealed their candidate LFN.
func recoverReferenceAliases(hc *http.Client, st *httpStats, ac *attackConfig, timedOut func() bool) int {
	if !args.CrawlReferences || ac == nil || ac.autocomplete == "none" || ac.references == nil {
		return 0
	}
	method := autocompleteProbeMethod(ac.autocomplete)
	var recovered int64

	concurrency := args.Concurrency
	if concurrency < 1 {
		concurrency = 1 // an unset -c (e.g. a hand-built arguments{} in tests) must not deadlock a 0-buffered channel
	}
	sem := make(chan struct{}, concurrency)
	wg := new(sync.WaitGroup)
	// Findings are collected here and printed after wg.Wait() on the CALLING
	// (main Scan) goroutine — NOT inline from the worker below. Under --parallel the
	// per-host output sink is keyed to the main goroutine, so a printHuman from one of
	// these workers reaches no sink and escapes straight to stdout, landing under
	// whichever host block happens to be flushing (a REF-RECOVER for host A printed
	// under host B). Buffering matches how sibling.go / collision.go already do it.
	var linesMu sync.Mutex
	var lines []string
	for _, br := range observedRecoveryAliases(ac) {
		// --maxtime soft budget, checked between aliases — see sibling.go's
		// recoverSiblingAliases for the fuller rationale.
		if timedOut != nil && timedOut() {
			break
		}
		br := br
		wg.Add(1)
		go func() {
			sem <- struct{}{}
			defer func() { <-sem; wg.Done() }()
			baseURL := recoveryBaseURL(br)
			for _, candidate := range referenceFilenameCandidates(ac, br) {
				candidatePath := pathEscape(candidate.record.filename + candidate.record.extension)
				ac.autocompleteMutex.Lock()
				if _, exists := ac.foundFiles[foundFileKey(candidatePath)]; exists {
					ac.autocompleteMutex.Unlock()
					continue
				}
				ac.autocompleteMutex.Unlock()

				res, matched, err := probeAutocompleteCandidate(hc, st, ac, br, baseURL, candidate)
				if err != nil {
					log.WithFields(log.Fields{"err": err, "method": method, "url": baseURL + candidatePath}).Info("Reference recovery check error")
					continue
				}
				if !matched {
					continue
				}

				ac.autocompleteMutex.Lock()
				if _, exists := ac.foundFiles[foundFileKey(candidatePath)]; exists {
					ac.autocompleteMutex.Unlock()
					continue
				}
				rememberConfirmedStem(ac, br, candidate, baseURL)
				markResolvedFile(ac, br, baseURL, candidatePath)
				ac.autocompleteMutex.Unlock()
				enrichResolvedFile(hc, st, ac, br, baseURL, candidatePath)

				atomic.AddInt64(&recovered, 1)
				group := shortCollisionGroup(br)
				verified := candidateVerifiesOrdinal(br, candidatePath)
				if args.Output == "human" {
					ordinal := "ordinal unverified"
					if verified {
						ordinal = "exact alias path"
					}
					// Collect, don't print here: a worker goroutine has no host sink, so
					// an inline printHuman would escape to the wrong host's block (see the
					// linesMu declaration above). The main goroutine prints after wg.Wait().
					line := fmt.Sprintf("  %s %s -> %s (%s from %s; %s/%s; %s; status %d)",
						color.HiGreenString("[REF-RECOVER]"), group,
						color.HiGreenString(baseURL+candidatePath), candidate.matchType,
						candidate.source, ac.autocomplete, method, ordinal, res.StatusCode)
					linesMu.Lock()
					lines = append(lines, line)
					linesMu.Unlock()
				} else {
					printJSON(resultOutput{
						Type: "recovery", FullMatch: true, BaseUrl: baseURL,
						File: br.file, Tilde: br.tilde, Ext: br.ext, Fullname: candidatePath,
						MatchType: candidate.matchType, Status: res.StatusCode,
						CollisionGroup: group, OrdinalVerified: boolPointer(verified),
						Oracle: ac.autocomplete, Method: method,
					})
				}
			}
		}()
	}
	wg.Wait()
	// Printed on the calling goroutine so the lines land in this host's sink.
	for _, line := range lines {
		printHuman(line)
	}
	return int(recovered)
}
