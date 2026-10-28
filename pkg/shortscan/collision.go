package shortscan

import (
	"fmt"
	"net/http"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
	"github.com/thezakman/shortscan/pkg/hashrecover"
	"github.com/thezakman/shortscan/pkg/shortutil"
)

// hashedAliasFields splits a checksummed 8.3 stem such as "PR45F4" into its
// one-or-two-character prefix ("PR") and the embedded four-hex checksum ("45F4").
// It returns ok=false for a classic stem whose final four characters are not all
// hexadecimal (for example "PRIMAX").
func hashedAliasFields(file string) (prefix, checksum string, ok bool) {
	upper := strings.ToUpper(file)
	if checksumRegex == nil || !checksumRegex.MatchString(upper) || len(upper) < 5 {
		return "", "", false
	}
	return upper[:len(upper)-4], upper[len(upper)-4:], true
}

// maskCache memoises meet-in-the-middle results. A given mask + alphabet +
// checksum is deterministic, so repeated hashed aliases never recompute.
var maskCache sync.Map

// maskTruncated is set when any grammar hit --checksum-limit. The advisory is
// deferred to the end-of-run summary (printFinishedStats) so it never interleaves
// with the enumeration results.
var maskTruncated int32

func recoverMaskCached(mask, alphabet, checksum string, limit int) []string {
	// hashrecover.RecoverMask errors on limit <= 0; normalize here once so every
	// caller gets the same "unset/invalid means the CLI default" behavior instead
	// of each call site having to remember to default it (checksumMaskCandidates
	// already did; collisionAncestryCandidates did not, so an embedder that builds
	// arguments{} directly with ChecksumLimit left at its zero value silently got
	// zero mask-derived candidates instead of a defaulted search).
	if limit <= 0 {
		limit = 256
	}
	key := mask + "\x00" + alphabet + "\x00" + checksum + "\x00" + strconv.Itoa(limit)
	if cached, ok := maskCache.Load(key); ok {
		return cached.([]string)
	}
	names, stats, err := hashrecover.RecoverMask(mask, alphabet, checksum, limit)
	if err != nil {
		log.WithFields(log.Fields{"mask": mask, "checksum": checksum, "err": err}).Info("checksum-mask recovery skipped")
		names = nil
	} else if stats.Truncated {
		atomic.StoreInt32(&maskTruncated, 1)
	}
	maskCache.Store(key, names)
	return names
}

// maskExtension83 returns the 8.3 extension implied by a mask's fixed extension,
// e.g. "App_Web_*.dll" -> "DLL". Empty when the mask has no extension.
func maskExtension83(mask string) string {
	_, extension := splitLongName(mask)
	if extension == "" {
		return ""
	}
	_, _, e83 := shortutil.Gen8dot3("x", extension)
	return e83
}

// maskLiteralPrefix83 returns the 8.3 filename prefix implied by the fixed leading
// characters of a mask (up to the first '?' or '*'), e.g. "Primax*.dll" ->
// "PRIMAX". It lets checksumMaskCandidates skip a mask that cannot match a given
// hashed-alias prefix before running the expensive search.
func maskLiteralPrefix83(mask string) string {
	literal := mask
	if i := strings.IndexAny(mask, "?*"); i >= 0 {
		literal = mask[:i]
	}
	filename, _ := splitLongName(literal)
	if filename == "" {
		filename = literal
	}
	_, f83, _ := shortutil.Gen8dot3(filename, "")
	return f83
}

// expandMask turns a --checksum-mask into the concrete '?'-only masks the
// meet-in-the-middle search accepts. A mask with no '*' is used as-is. A mask
// with one '*' is expanded to a variable-length run of '?' from length 1 up to
// --checksum-max-length, stopping early once a longer run would exceed the leaf
// budget (longer only grows the search). This lets an operator write
// 'App_Web_*.dll' instead of guessing the exact number of '?'.
func expandMask(mask, alphabet string) []string {
	if !strings.Contains(mask, "*") {
		if strings.Contains(mask, "?") {
			return []string{mask}
		}
		return nil
	}
	maxLen := args.ChecksumMaxLength
	if maxLen <= 0 {
		maxLen = 8
	}
	var concrete []string
	for length := 1; length <= maxLen; length++ {
		candidate := strings.Replace(mask, "*", strings.Repeat("?", length), 1)
		forward, backward := hashrecover.EstimateLeaves(candidate, alphabet)
		if forward > hashrecover.DefaultMaxForwardLeaves || backward > hashrecover.DefaultMaxBackwardLeaves {
			break
		}
		concrete = append(concrete, candidate)
	}
	return concrete
}

// splitLongName splits a reconstructed long name into filename and dotted
// extension using the same last-dot rule the rest of the tool uses.
func splitLongName(name string) (filename, extension string) {
	if dot := strings.LastIndex(name, "."); dot > 0 && name[0] != '.' {
		return name[:dot], name[dot:]
	}
	return name, ""
}

// checksumMaskCandidates reconstructs long-name candidates for a hashed alias
// from every configured --checksum-mask. Each candidate is 8.3-consistent with
// the observed alias (same short extension and prefix) and still goes through the
// normal HTTP oracle before it is reported.
func checksumMaskCandidates(br baseRequest) []filenameCandidate {
	if len(args.ChecksumMasks) == 0 {
		return nil
	}
	prefix, checksum, ok := hashedAliasFields(br.file)
	if !ok {
		return nil
	}
	shortExtension := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
	limit := args.ChecksumLimit
	if limit <= 0 {
		limit = 256
	}
	seen := make(map[string]struct{})
	var result []filenameCandidate
	for _, mask := range args.ChecksumMasks {
		if len(result) >= limit {
			break
		}
		// Cheap pre-filters: a mask whose fixed extension or literal prefix cannot
		// match this alias never runs the meet-in-the-middle search (so it neither
		// wastes requests nor warns) for it.
		if e83 := maskExtension83(mask); e83 != "" && !strings.EqualFold(e83, shortExtension) {
			continue
		}
		if p83 := maskLiteralPrefix83(mask); p83 != "" &&
			!strings.HasPrefix(p83, prefix) && !strings.HasPrefix(prefix, p83) {
			continue
		}
		for _, concrete := range expandMask(mask, args.ChecksumAlphabet) {
			if len(result) >= limit {
				break
			}
			for _, name := range recoverMaskCached(concrete, args.ChecksumAlphabet, checksum, limit) {
				filename, extension := splitLongName(name)
				if filename == "" || isDotSegment(filename) {
					continue
				}
				_, filename83, extension83 := shortutil.Gen8dot3(filename, extension)
				if !strings.EqualFold(extension83, shortExtension) {
					continue
				}
				if !strings.HasPrefix(filename83, prefix) {
					continue
				}
				key := strings.ToLower(filename + extension)
				if _, exists := seen[key]; exists {
					continue
				}
				seen[key] = struct{}{}
				result = append(result, filenameCandidate{
					record: wordlistRecord{
						filename: filename, extension: extension,
						filename83: filename83, extension83: extension83,
					},
					matchType: "checksum-mask",
					source:    mask,
					checksum:  checksum,
				})
				if len(result) >= limit {
					break
				}
			}
		}
	}
	sort.Slice(result, func(i, j int) bool {
		return strings.ToLower(result[i].record.filename+result[i].record.extension) <
			strings.ToLower(result[j].record.filename+result[j].record.extension)
	})
	return result
}

// collisionFamily is a classic six-character prefix whose ordinals 1..4 were all
// observed for the same short extension (a saturated family).
type collisionFamily struct {
	stem     string // uppercase classic prefix
	ext      string // uppercase short extension, no dot
	ordinals map[int]struct{}
}

func aliasOrdinal(tilde string) int {
	digits := strings.TrimLeft(tilde, "~")
	value, err := strconv.Atoi(digits)
	if err != nil {
		return 0
	}
	return value
}

// saturatedFamilies groups observed classic aliases by (prefix, extension) and
// keeps only those with all of ~1, ~2, ~3 and ~4 present. That saturation is the
// documented precondition for Windows switching to the two-character-plus-
// checksum alias form, so it is required before proposing any ancestry.
func saturatedFamilies(aliases []baseRequest) []collisionFamily {
	grouped := make(map[string]*collisionFamily)
	for _, br := range aliases {
		if br.file == "" {
			continue
		}
		if _, _, hashed := hashedAliasFields(br.file); hashed {
			continue
		}
		ordinal := aliasOrdinal(br.tilde)
		if ordinal == 0 {
			continue
		}
		stem := strings.ToUpper(br.file)
		ext := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
		key := stem + "\x00" + ext
		family := grouped[key]
		if family == nil {
			family = &collisionFamily{stem: stem, ext: ext, ordinals: make(map[int]struct{})}
			grouped[key] = family
		}
		family.ordinals[ordinal] = struct{}{}
	}
	var result []collisionFamily
	for _, family := range grouped {
		saturated := true
		for ordinal := 1; ordinal <= 4; ordinal++ {
			if _, exists := family.ordinals[ordinal]; !exists {
				saturated = false
				break
			}
		}
		if saturated {
			result = append(result, *family)
		}
	}
	sort.Slice(result, func(i, j int) bool {
		if result[i].stem != result[j].stem {
			return result[i].stem < result[j].stem
		}
		return result[i].ext < result[j].ext
	})
	return result
}

// familiesForAlias returns the saturated families that could be the ancestry of a
// hashed alias: same short extension, and a classic stem that starts with the
// alias's exposed prefix. More than one is intentionally allowed and preserved.
func familiesForAlias(families []collisionFamily, prefix, aliasExt string) []collisionFamily {
	ext := strings.TrimPrefix(strings.ToUpper(aliasExt), ".")
	prefix = strings.ToUpper(prefix)
	var linked []collisionFamily
	for _, family := range families {
		if strings.EqualFold(family.ext, ext) && strings.HasPrefix(family.stem, prefix) {
			linked = append(linked, family)
		}
	}
	return linked
}

func familyLabels(families []collisionFamily) []string {
	labels := make([]string, 0, len(families))
	for _, family := range families {
		label := family.stem + "~*"
		if family.ext != "" {
			label += "." + family.ext
		}
		labels = append(labels, label)
	}
	return labels
}

// collisionAncestryCandidates reconstructs long-name candidates for a hashed
// alias by requiring the classic prefix of a saturated family plus the exact
// embedded checksum. Candidate names are drawn from the loaded wordlist, crawled
// references and any --checksum-mask; the family stem and the 16-bit checksum
// together are what select them. Every survivor is still HTTP-verified.
func collisionAncestryCandidates(ac *attackConfig, br baseRequest, families []collisionFamily) []filenameCandidate {
	_, checksum, ok := hashedAliasFields(br.file)
	if !ok || len(families) == 0 {
		return nil
	}
	aliasExt := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
	labels := familyLabels(families)
	result := make(map[string]filenameCandidate)
	consider := func(filename, extension, source string) {
		if filename == "" || isDotSegment(filename) {
			return
		}
		_, filename83, extension83 := shortutil.Gen8dot3(filename, extension)
		if !strings.EqualFold(extension83, aliasExt) {
			return
		}
		belongs := false
		for _, family := range families {
			if strings.EqualFold(filename83, family.stem) {
				belongs = true
				break
			}
		}
		if !belongs {
			return
		}
		if !strings.EqualFold(shortutil.Checksum(filename+extension), checksum) {
			return
		}
		key := strings.ToLower(filename + extension)
		if _, exists := result[key]; exists {
			return
		}
		result[key] = filenameCandidate{
			record: wordlistRecord{
				filename: filename, extension: extension,
				filename83: filename83, extension83: extension83,
			},
			matchType: "collision-ancestry",
			source:    source,
			checksum:  checksum,
			families:  labels,
		}
	}

	if ac.wordlist != nil {
		if records, _ := ac.wordlist.records(); records != nil {
			for _, record := range records {
				consider(record.filename, record.extension, "wordlist")
			}
		}
	}
	if args.CrawlReferences && ac.references != nil {
		for _, evidence := range ac.references.recordsFor(br.url) {
			consider(evidence.record.filename, evidence.record.extension, evidence.source)
		}
	}
	for _, mask := range args.ChecksumMasks {
		for _, concrete := range expandMask(mask, args.ChecksumAlphabet) {
			for _, name := range recoverMaskCached(concrete, args.ChecksumAlphabet, checksum, args.ChecksumLimit) {
				filename, extension := splitLongName(name)
				consider(filename, extension, mask)
			}
		}
	}

	candidates := make([]filenameCandidate, 0, len(result))
	for _, candidate := range result {
		candidates = append(candidates, candidate)
	}
	sort.Slice(candidates, func(i, j int) bool {
		return strings.ToLower(candidates[i].record.filename+candidates[i].record.extension) <
			strings.ToLower(candidates[j].record.filename+candidates[j].record.extension)
	})
	return candidates
}

// recoverCollisionAncestryAliases is a deterministic second pass. Saturated
// families are only complete once every ordinal has been enumerated, so ancestry
// links must be built after the concurrent workers finish, mirroring the sibling
// recovery pass.
func recoverCollisionAncestryAliases(hc *http.Client, st *httpStats, ac *attackConfig, timedOut func() bool) int {
	if !args.CollisionAncestry || ac == nil || ac.autocomplete == "none" {
		return 0
	}
	aliases := observedRecoveryAliases(ac)
	families := saturatedFamilies(aliases)
	if len(families) == 0 {
		return 0
	}
	method := autocompleteProbeMethod(ac.autocomplete)
	var recovered int64
	var linesMu sync.Mutex
	var lines []string

	concurrency := args.Concurrency
	if concurrency < 1 {
		concurrency = 1 // an unset -c (e.g. a hand-built arguments{} in tests) must not deadlock a 0-buffered channel
	}
	sem := make(chan struct{}, concurrency)
	wg := new(sync.WaitGroup)
	for _, br := range aliases {
		// --maxtime soft budget, checked between aliases — see sibling.go's
		// recoverSiblingAliases for the fuller rationale.
		if timedOut != nil && timedOut() {
			break
		}
		br := br
		prefix, _, ok := hashedAliasFields(br.file)
		if !ok {
			continue
		}
		linked := familiesForAlias(families, prefix, br.ext)
		if len(linked) == 0 {
			continue
		}
		labels := familyLabels(linked)
		wg.Add(1)
		go func() {
			sem <- struct{}{}
			defer func() { <-sem; wg.Done() }()
			baseURL := recoveryBaseURL(br)
			for _, candidate := range collisionAncestryCandidates(ac, br, linked) {
				candidatePath := pathEscape(candidate.record.filename + candidate.record.extension)
				ac.autocompleteMutex.Lock()
				if _, exists := ac.foundFiles[foundFileKey(candidatePath)]; exists {
					ac.autocompleteMutex.Unlock()
					continue
				}
				ac.autocompleteMutex.Unlock()

				res, matched, err := probeAutocompleteCandidate(hc, st, ac, br, baseURL, candidate)
				if err != nil {
					log.WithFields(log.Fields{"err": err, "method": method, "url": baseURL + candidatePath}).Info("Collision-ancestry check error")
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
				if args.Output == "human" {
					profile := ac.autocomplete + "/" + method
					line := fmt.Sprintf("  %s -> %s (ck=%s families=%s from %s; %s; ordinal unverified; status %d)",
						group, color.HiGreenString(baseURL+candidatePath), candidate.checksum,
						strings.Join(labels, ","), candidate.source, profile, res.StatusCode)
					linesMu.Lock()
					lines = append(lines, line)
					linesMu.Unlock()
				} else {
					printJSON(resultOutput{
						Type: "recovery", FullMatch: true, BaseUrl: baseURL,
						File: br.file, Tilde: br.tilde, Ext: br.ext, Fullname: candidatePath,
						MatchType: "collision-ancestry", Status: res.StatusCode,
						CollisionGroup: group, OrdinalVerified: boolPointer(false),
						Oracle: ac.autocomplete, Method: method,
						Checksum: candidate.checksum, DerivedFrom: candidate.source,
						CandidateFamilies: labels,
					})
				}
			}
		}()
	}
	wg.Wait()
	if len(lines) > 0 {
		beginSection(ac)
		printHuman(color.HiCyanString("[COLLISION-ANCESTRY] %s recovered", pluralCount(len(lines), "name", "names")))
		for _, line := range lines {
			printHuman(line)
		}
	}
	return int(recovered)
}
