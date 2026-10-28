package shortscan

import (
	"fmt"
	"net/http"
	nurl "net/url"
	"sort"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
	"github.com/thezakman/shortscan/pkg/shortutil"
)

type confirmedStem struct {
	stem        string
	source      string
	inferred    bool
	variantSeed bool
}

// siblingStemKnowledge stores HTTP-confirmed stems plus quarantined manifest
// inferences. Confirmed stems behave globally as before. An inferred stem may
// only generate bounded candidates for readable extensions, each of which must
// pass the ordinary HTTP oracle before it is reported.
type siblingStemKnowledge struct {
	sync.RWMutex
	byOrigin map[string]map[string]map[string]confirmedStem
}

const maxSiblingStemsPerPrefix = 32

func newSiblingStemKnowledge() *siblingStemKnowledge {
	return &siblingStemKnowledge{byOrigin: make(map[string]map[string]map[string]confirmedStem)}
}

func originKey(rawURL string) string {
	parsed, err := nurl.Parse(rawURL)
	if err != nil || parsed.Scheme == "" || parsed.Host == "" {
		return ""
	}
	return strings.ToLower(parsed.Scheme + "://" + parsed.Host)
}

func rememberSiblingStem(ac *attackConfig, br baseRequest, candidate filenameCandidate, baseURL string, inferred bool) {
	if !args.SiblingRecovery || ac == nil || ac.siblingStems == nil || candidate.record.filename == "" ||
		strings.HasPrefix(candidate.matchType, "short-name") {
		return
	}
	shortExtension := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
	_, filename83, extension83 := shortutil.Gen8dot3(candidate.record.filename, candidate.record.extension)
	if !strings.EqualFold(filename83, br.file) || !strings.EqualFold(extension83, shortExtension) {
		// Checksummed aliases cannot safely seed a plain six-character prefix.
		return
	}
	origin := originKey(br.url)
	if origin == "" {
		return
	}
	prefix := strings.ToUpper(br.file)
	stemKey := strings.ToLower(candidate.record.filename)
	knowledge := ac.siblingStems
	knowledge.Lock()
	defer knowledge.Unlock()
	if knowledge.byOrigin[origin] == nil {
		knowledge.byOrigin[origin] = make(map[string]map[string]confirmedStem)
	}
	if knowledge.byOrigin[origin][prefix] == nil {
		knowledge.byOrigin[origin][prefix] = make(map[string]confirmedStem)
	}
	stems := knowledge.byOrigin[origin][prefix]
	if existing, exists := stems[stemKey]; exists {
		// An HTTP-confirmed recovery upgrades an earlier request-filtered inference.
		if existing.inferred && !inferred {
			stems[stemKey] = confirmedStem{
				stem: candidate.record.filename, variantSeed: existing.variantSeed,
				source: baseURL + pathEscape(candidate.record.filename+candidate.record.extension),
			}
		}
		return
	}
	if len(stems) >= maxSiblingStemsPerPrefix {
		return
	}
	source := baseURL + pathEscape(candidate.record.filename+candidate.record.extension)
	if inferred {
		source += " (request-filtered inference)"
	}
	stems[stemKey] = confirmedStem{
		stem: candidate.record.filename, source: source, inferred: inferred, variantSeed: inferred,
	}
}

func rememberConfirmedStem(ac *attackConfig, br baseRequest, candidate filenameCandidate, baseURL string) {
	rememberSiblingStem(ac, br, candidate, baseURL, false)
}

// rememberInferredStem keeps a request-filtered manifest guess quarantined as a
// seed. The inferred name itself remains unconfirmed, but an exact, readable
// sibling derived from its stem must still pass the normal HTTP oracle before it
// is reported. A wrong inference therefore costs bounded probes, not a finding.
func rememberInferredStem(ac *attackConfig, br baseRequest, candidate filenameCandidate, baseURL string) {
	rememberSiblingStem(ac, br, candidate, baseURL, true)
}

var inferredSiblingSuffixes = [...]string{
	"", ".Production", ".Development", ".Staging", ".Local",
	".Debug", ".Release", ".Backup", ".Old", ".Copy",
	"_Production", "_Development", "_Staging", "_Local", "_Backup", "-backup",
}

func (knowledge *siblingStemKnowledge) stemsFor(br baseRequest) []confirmedStem {
	if knowledge == nil {
		return nil
	}
	origin := originKey(br.url)
	prefix := strings.ToUpper(br.file)
	knowledge.RLock()
	stems := knowledge.byOrigin[origin][prefix]
	result := make([]confirmedStem, 0, len(stems))
	for _, stem := range stems {
		result = append(result, stem)
	}
	knowledge.RUnlock()
	sort.Slice(result, func(i, j int) bool {
		return strings.ToLower(result[i].stem) < strings.ToLower(result[j].stem)
	})
	return result
}

func siblingFilenameCandidates(ac *attackConfig, br baseRequest, includeKnownExtensions bool) []filenameCandidate {
	if !args.SiblingRecovery || ac == nil || ac.siblingStems == nil || br.file == "" {
		return nil
	}
	shortExtension := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
	extensions := []string{br.ext}
	if includeKnownExtensions && shortExtension != "" {
		for _, extension := range wellKnownExtensions {
			_, _, extension83 := shortutil.Gen8dot3("x", extension)
			if strings.EqualFold(extension83, shortExtension) {
				extensions = append(extensions, extension)
			}
		}
	}
	candidates := make(map[string]filenameCandidate)
	for _, evidence := range ac.siblingStems.stemsFor(br) {
		for _, extension := range extensions {
			// Never turn a blocked-name inference into another blocked-name claim.
			// Its only purpose is to discover a readable sibling that can be actively
			// verified (for example AppSettings.config -> AppSettings.Production.txt).
			if evidence.variantSeed && isRequestFilteredName("x"+extension) {
				continue
			}
			suffixes := inferredSiblingSuffixes[:1]
			if evidence.variantSeed {
				suffixes = inferredSiblingSuffixes[:]
			}
			for _, suffix := range suffixes {
				stem := evidence.stem + suffix
				_, filename83, extension83 := shortutil.Gen8dot3(stem, extension)
				if !strings.EqualFold(filename83, br.file) || !strings.EqualFold(extension83, shortExtension) {
					continue
				}
				key := strings.ToLower(stem + extension)
				if _, exists := candidates[key]; exists {
					continue
				}
				matchType := "sibling-stem"
				if evidence.variantSeed {
					matchType = "manifest-sibling-variant"
				}
				candidates[key] = filenameCandidate{
					record: wordlistRecord{
						filename: stem, extension: extension,
						filename83: filename83, extension83: extension83,
					},
					matchType: matchType,
					source:    evidence.source,
				}
			}
		}
	}
	result := make([]filenameCandidate, 0, len(candidates))
	for _, candidate := range candidates {
		result = append(result, candidate)
	}
	sort.Slice(result, func(i, j int) bool {
		return strings.ToLower(result[i].record.filename+result[i].record.extension) <
			strings.ToLower(result[j].record.filename+result[j].record.extension)
	})
	return result
}

// probeManifestSiblingRead turns a confirmed manifest-derived sibling into a
// controlled content check. The exact long name has already passed the selected
// existence oracle; this GET is accepted only when a random same-extension name
// does not also return bytes, preventing soft-404/serve-everything findings.
func probeManifestSiblingRead(hc *http.Client, st *httpStats, baseURL, candidatePath string) []string {
	if !(args.Auto || args.Full) {
		return nil
	}
	url := baseURL + candidatePath
	res, body, err := fetchBody(hc, st, "GET", url, 1<<16)
	if err != nil || res == nil || res.StatusCode/100 != 2 || len(body) == 0 {
		return nil
	}
	dot := strings.LastIndex(candidatePath, ".")
	extension := ""
	if dot >= 0 {
		extension = candidatePath[dot:]
	}
	control := randAlnum(12) + extension
	if cres, cbody, _ := fetchBody(hc, st, "GET", baseURL+control, 2048); cres != nil && cres.StatusCode/100 == 2 && len(cbody) > 0 {
		return nil
	}

	disclosureType := "readable manifest sibling"
	severity := "medium"
	if disclosed, dt := inspectDisclosure(body); disclosed {
		disclosureType, severity = dt, "high"
	} else {
		lower := strings.ToLower(string(body))
		for _, marker := range []string{"password", "passwd", "connectionstring", "secret", "api_key", "apikey", "token", "private key"} {
			if strings.Contains(lower, marker) {
				disclosureType, severity = "secret/configuration markers", "high"
				break
			}
		}
	}

	lines := []string{
		"    " + color.HiRedString("[MANIFEST-SIBLING-READ/%s] %s served %d bytes (%s); random same-extension control did not serve", severity, url, len(body), disclosureType),
	}
	if saved, path, _ := saveDisclosedFile(hc, st, url, candidatePath); saved {
		lines = append(lines, "    "+color.HiGreenString("    saved -> %s", path))
	} else if path != "" {
		lines = append(lines, "    "+color.HiBlackString("    %s", path))
	}
	if args.Output != "human" {
		printJSON(resultOutput{
			Type: "disclosure", FullMatch: true, SourceDisclosure: true,
			DisclosureType: disclosureType, BaseUrl: baseURL, Fullname: candidatePath,
			Status: res.StatusCode,
		})
	}
	return lines
}

// recoverSiblingAliases is a deterministic second pass. Enumeration runs
// concurrently, so an archive alias may be completed before the extensionless
// sibling that reveals its long stem. Waiting for the short-name workers and
// probing only newly derived sibling candidates removes that ordering race
// without repeating the whole wordlist.
func recoverSiblingAliases(hc *http.Client, st *httpStats, ac *attackConfig, timedOut func() bool) int {
	if !args.SiblingRecovery || ac == nil || ac.autocomplete == "none" || ac.siblingStems == nil {
		return 0
	}
	aliases := observedRecoveryAliases(ac)

	includeKnown := args.KnownExtensions || args.ProbeCandidates || candidateOutputWriter != nil
	method := autocompleteProbeMethod(ac.autocomplete)
	var recovered int64
	var linesMu sync.Mutex
	var lines []string

	// Each alias's own candidates are tried one at a time (unchanged, preserves this
	// alias's ordering/output), but different aliases are independent of each other,
	// so they run concurrently, bounded by -c — mirroring the worker-pool pattern
	// already used for charset discovery and the main enumeration loop. Critically,
	// ac.autocompleteMutex below is only held around the ac.foundFiles check/mark, NOT
	// across probeAutocompleteCandidate's network round-trip: holding it across the
	// HTTP call would serialize every goroutine on this one lock and defeat the
	// parallelism entirely.
	concurrency := args.Concurrency
	if concurrency < 1 {
		// A zero-buffered channel deadlocks every sender (nothing else ever
		// receives), so an unset/zero -c — the default in a hand-built
		// arguments{} literal, e.g. in tests — must still allow at least one
		// in-flight probe rather than hang the whole pass forever.
		concurrency = 1
	}
	sem := make(chan struct{}, concurrency)
	wg := new(sync.WaitGroup)
	for _, br := range aliases {
		// --maxtime is a soft per-URL budget checked between units of work (not
		// a preemptive abort of in-flight requests, which stay bounded by -t) —
		// see cli.go's flag doc. Checked once per alias, before starting new
		// work, same spirit as Scan()'s own queued-paths check.
		if timedOut != nil && timedOut() {
			break
		}
		br := br
		wg.Add(1)
		go func() {
			sem <- struct{}{}
			defer func() { <-sem; wg.Done() }()
			baseURL := recoveryBaseURL(br)
			for _, candidate := range siblingFilenameCandidates(ac, br, includeKnown) {
				candidatePath := pathEscape(candidate.record.filename + candidate.record.extension)
				ac.autocompleteMutex.Lock()
				if _, exists := ac.foundFiles[foundFileKey(candidatePath)]; exists {
					ac.autocompleteMutex.Unlock()
					continue
				}
				ac.autocompleteMutex.Unlock()

				res, matched, err := probeAutocompleteCandidate(hc, st, ac, br, baseURL, candidate)
				if err != nil {
					log.WithFields(log.Fields{"err": err, "method": method, "url": baseURL + candidatePath}).Info("Sibling recovery check error")
					continue
				}
				if !matched {
					continue
				}

				// Re-check under lock before marking: two aliases can independently
				// derive the same sibling candidatePath and both reach this point
				// concurrently, having each probed it once (harmless duplicate
				// request) — only the first to arrive here should record/report it.
				// markResolvedFile itself makes further network calls when
				// --inspect-source/--mutate-ext are set (enabled by --full) — held
				// under lock here (matching this function's existing convention for
				// that call), so those two opt-in enrichments still serialize
				// per-match under heavy concurrency; the exploratory candidate probing
				// above, the bulk of the work, does not.
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
				longName := candidate.record.filename + candidate.record.extension
				if args.Output == "human" {
					profile := ac.autocomplete + "/" + method
					status := res.StatusCode
					if candidate.matchType == "manifest-sibling-variant" {
						status = displayStatus(hc, st, ac.autocomplete, method, baseURL+candidatePath, status)
					}
					line := fmt.Sprintf("  %s -> %s (from %s; %s; ordinal unverified; status %d)",
						group, color.HiGreenString(baseURL+candidatePath), candidate.source, profile, status)
					var readLines []string
					if candidate.matchType == "manifest-sibling-variant" {
						readLines = probeManifestSiblingRead(hc, st, baseURL, candidatePath)
					}
					linesMu.Lock()
					lines = append(lines, line)
					lines = append(lines, readLines...)
					linesMu.Unlock()
					// A recovered web.config / key / appsettings is only useful if it can
					// actually be READ. Don't leave a bare "status 403" (the expected block):
					// actively try the 8.3-alias read and report the verdict (leak, IIS-patch
					// wall, or front-end wall + the cross-stack pointer).
					if label, ok := sensitiveDisclosureLabel(longName); ok {
						verdict := probeSensitiveAliasRead(hc, st, ac, br, baseURL, longName, label)
						linesMu.Lock()
						lines = append(lines, verdict...)
						linesMu.Unlock()
					}
				} else {
					status := res.StatusCode
					if candidate.matchType == "manifest-sibling-variant" {
						status = displayStatus(hc, st, ac.autocomplete, method, baseURL+candidatePath, status)
					}
					printJSON(resultOutput{
						Type: "recovery", FullMatch: true, BaseUrl: baseURL,
						File: br.file, Tilde: br.tilde, Ext: br.ext, Fullname: candidatePath,
						MatchType: candidate.matchType, Status: status,
						CollisionGroup: group, OrdinalVerified: boolPointer(false),
						Oracle: ac.autocomplete, Method: method,
					})
					if candidate.matchType == "manifest-sibling-variant" {
						probeManifestSiblingRead(hc, st, baseURL, candidatePath)
					}
					// Same active read in machine modes: a confirmed leak of a sensitive
					// file must surface (JSON disclosure record) regardless of output format.
					if label, ok := sensitiveDisclosureLabel(longName); ok {
						probeSensitiveAliasRead(hc, st, ac, br, baseURL, longName, label)
					}
				}
			}
		}()
	}
	wg.Wait()

	if len(lines) > 0 {
		beginSection(ac)
		printHuman(color.HiCyanString("[SIBLING] %s recovered", pluralCount(int(recovered), "name", "names")))
		for _, line := range lines {
			printHuman(line)
		}
	}
	return int(recovered)
}
