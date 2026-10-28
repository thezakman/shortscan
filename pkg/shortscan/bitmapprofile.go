package shortscan

import (
	"fmt"
	"net/http"
	nurl "net/url"
	"sort"
	"strings"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
)

type bitmapCapabilityObservation struct {
	Available bool
	Present   bool
	Reason    string
	Candidate allowCopySignature
	Control   allowCopySignature
}

type bitmapProfileOutput struct {
	Type                    string `json:"type"`
	URL                     string `json:"url"`
	OracleAvailable         bool   `json:"oracleavailable"`
	IndexAllocation         bool   `json:"indexallocation"`
	Bitmap                  bool   `json:"bitmap"`
	NamedBitmap             bool   `json:"namedbitmap"`
	Classification          string `json:"classification"`
	HistoricalHighWatermark bool   `json:"historicalhighwatermark"`
	Note                    string `json:"note,omitempty"`
	// BaselineUnavailable is true only when the base H40 PROPFIND/Allow capability
	// oracle itself never worked (index.Available == false in probeBitmapProfileTarget)
	// — as opposed to OracleAvailable being false merely because the ::$BITMAP/
	// :$I30:$BITMAP follow-up probes were flaky on an otherwise-confirmed directory.
	// Only the former means the whole origin is unusable; see runAutoBitmapProfiles.
	BaselineUnavailable bool `json:"baselineunavailable,omitempty"`
}

func normalizeBitmapProfileTarget(raw string) (baseURL, candidatePath, displayURL string, err error) {
	value := strings.TrimSpace(raw)
	if !strings.Contains(value, "://") {
		value = "https://" + value
	}
	u, err := nurl.Parse(value)
	if err != nil {
		return "", "", "", err
	}
	u.Scheme = strings.ToLower(u.Scheme)
	if (u.Scheme != "http" && u.Scheme != "https") || u.Host == "" || u.Opaque != "" {
		return "", "", "", fmt.Errorf("URL must use http or https and include a host")
	}
	if u.RawQuery != "" || u.ForceQuery || u.Fragment != "" {
		return "", "", "", fmt.Errorf("URL must identify one directory without query or fragment")
	}
	escapedPath := strings.TrimSuffix(u.EscapedPath(), "/")
	if escapedPath == "" || escapedPath == "/" {
		return "", "", "", fmt.Errorf("the site root has no final directory component to suffix with $BITMAP")
	}
	slash := strings.LastIndexByte(escapedPath, '/')
	if slash < 0 || slash == len(escapedPath)-1 {
		return "", "", "", fmt.Errorf("URL must end in a directory component")
	}
	candidatePath = escapedPath[slash+1:]
	decodedCandidate, decodeErr := nurl.PathUnescape(candidatePath)
	if decodeErr != nil || decodedCandidate == "." || decodedCandidate == ".." ||
		strings.ContainsAny(decodedCandidate, "/\\:") {
		return "", "", "", fmt.Errorf("final directory component must not contain separators, dot segments, or ADS syntax")
	}
	origin := (&nurl.URL{Scheme: u.Scheme, User: u.User, Host: u.Host}).String()
	baseURL = origin + escapedPath[:slash+1]
	displayURL = origin + escapedPath + "/"
	return baseURL, candidatePath, displayURL, nil
}

func bitmapSignaturesStable(values []allowCopySignature) (allowCopySignature, bool) {
	if len(values) == 0 {
		return allowCopySignature{}, false
	}
	first := values[0]
	for _, value := range values[1:] {
		if value != first {
			return first, false
		}
	}
	return first, true
}

// probeBitmapCapability uses the same H40 capability bit as allow-copy recovery,
// but classifies both presence and absence. Two same-shape controls and two full
// rounds are required; a raw 405 or a lone COPY token is never promoted.
func probeBitmapCapability(hc *http.Client, st *httpStats, baseURL, candidatePath, suffix string) (bitmapCapabilityObservation, error) {
	controls := [2]string{
		baseURL + randPath(len(candidatePath), 0, alphanum) + suffix,
		baseURL + randPath(len(candidatePath), 0, alphanum) + suffix,
	}
	candidateURL := baseURL + candidatePath + suffix
	candidateValues := make([]allowCopySignature, 0, 2)
	controlValues := [2][]allowCopySignature{{}, {}}
	for round := 0; round < 2; round++ {
		_, candidate, err := fetchAllowCopySignature(hc, st, candidateURL)
		if err != nil {
			return bitmapCapabilityObservation{}, err
		}
		candidateValues = append(candidateValues, candidate)
		for index, controlURL := range controls {
			_, control, controlErr := fetchAllowCopySignature(hc, st, controlURL)
			if controlErr != nil {
				return bitmapCapabilityObservation{}, controlErr
			}
			controlValues[index] = append(controlValues[index], control)
		}
	}

	candidate, candidateStable := bitmapSignaturesStable(candidateValues)
	controlOne, controlOneStable := bitmapSignaturesStable(controlValues[0])
	controlTwo, controlTwoStable := bitmapSignaturesStable(controlValues[1])
	observation := bitmapCapabilityObservation{Candidate: candidate, Control: controlOne}
	if !candidateStable || !controlOneStable || !controlTwoStable {
		observation.Reason = "candidate or controls changed across repetitions"
		return observation, nil
	}
	if controlOne != controlTwo || !usableAllowCopySignature(controlOne, false) {
		observation.Reason = "controls did not establish the 405 Allow-without-COPY baseline"
		return observation, nil
	}
	observation.Available = true
	if candidate == controlOne {
		observation.Reason = "stable capability absence"
		return observation, nil
	}
	if usableAllowCopySignature(candidate, true) && candidate.status == controlOne.status && candidate.allow == controlOne.allow {
		observation.Present = true
		observation.Reason = "COPY is the sole stable candidate/control difference"
		return observation, nil
	}
	observation.Available = false
	observation.Reason = "candidate differed from controls by more than COPY"
	return observation, nil
}

func classifyBitmapProfile(index, bitmap, named bitmapCapabilityObservation) (classification, note string, highWatermark bool) {
	if !index.Available {
		return "inconclusive", "the H40 PROPFIND/Allow capability oracle was unavailable or unstable", false
	}
	if !index.Present {
		return "not-a-confirmed-directory", "::$INDEX_ALLOCATION did not resolve under the calibrated oracle", false
	}
	if !bitmap.Available || !named.Available {
		return "inconclusive", "the bitmap forms were unavailable or unstable after the directory oracle resolved", false
	}
	if bitmap.Present != named.Present {
		return "inconclusive", "::$BITMAP and :$I30:$BITMAP disagreed", false
	}
	if bitmap.Present {
		return "materialized-directory-index", "$BITMAP proves a non-resident directory index now or at a historical high-water mark; it does not reveal the current child count", true
	}
	return "resident-directory-index", "the directory resolved but no allocated $BITMAP stream was observed", false
}

func probeBitmapProfileTarget(rawURL string, hc *http.Client, st *httpStats) (bitmapProfileOutput, error) {
	baseURL, candidatePath, displayURL, err := normalizeBitmapProfileTarget(rawURL)
	if err != nil {
		return bitmapProfileOutput{}, err
	}
	index, err := probeBitmapCapability(hc, st, baseURL, candidatePath, "::$INDEX_ALLOCATION")
	if err != nil {
		return bitmapProfileOutput{}, err
	}
	bitmap, named := bitmapCapabilityObservation{}, bitmapCapabilityObservation{}
	if index.Available && index.Present {
		bitmap, err = probeBitmapCapability(hc, st, baseURL, candidatePath, "::$BITMAP")
		if err != nil {
			return bitmapProfileOutput{}, err
		}
		named, err = probeBitmapCapability(hc, st, baseURL, candidatePath, ":$I30:$BITMAP")
		if err != nil {
			return bitmapProfileOutput{}, err
		}
	}
	classification, note, highWatermark := classifyBitmapProfile(index, bitmap, named)
	available := index.Available && (!index.Present || bitmap.Available && named.Available)
	return bitmapProfileOutput{
		Type: "bitmap-profile", URL: displayURL, OracleAvailable: available,
		IndexAllocation: index.Present, Bitmap: bitmap.Present, NamedBitmap: named.Present,
		Classification: classification, HistoricalHighWatermark: highWatermark, Note: note,
		BaselineUnavailable: !index.Available,
	}, nil
}

func emitBitmapProfile(profile bitmapProfileOutput) {
	if args.Output == "csv" {
		printJSON(resultOutput{
			Type: "bitmap-profile", FullMatch: profile.OracleAvailable && profile.IndexAllocation,
			BaseUrl: profile.URL, MatchType: profile.Classification, Method: "PROPFIND",
			Oracle: fmt.Sprintf("available=%t index=%t bitmap=%t namedbitmap=%t historicalhighwatermark=%t; %s",
				profile.OracleAvailable, profile.IndexAllocation, profile.Bitmap, profile.NamedBitmap,
				profile.HistoricalHighWatermark, profile.Note),
		})
	} else {
		printJSON(profile)
	}
	line := fmt.Sprintf("[BITMAP] %s index=%t bitmap=%t named=%t -> %s", profile.URL,
		profile.IndexAllocation, profile.Bitmap, profile.NamedBitmap, profile.Classification)
	if profile.Classification == "materialized-directory-index" {
		printHuman(color.HiGreenString(line))
	} else if profile.Classification == "resident-directory-index" {
		printHuman(color.HiCyanString(line))
	} else {
		printHuman(color.HiBlackString(line + " (" + profile.Note + ")"))
	}
}

func runBitmapProfiles(urls []string, hc *http.Client, st *httpStats) {
	for _, rawURL := range urls {
		profile, err := probeBitmapProfileTarget(rawURL, hc, st)
		if err != nil {
			printHuman(color.HiRedString("[BITMAP] %s: %v", rawURL, err))
			continue
		}
		emitBitmapProfile(profile)
	}
	printFinishedStats(st)
}

func autoBitmapTargets(currentURL string, chain []string, foundDirectories map[string]struct{}) []string {
	limit := 6
	if args.Full {
		limit = 24
	}
	seen := make(map[string]struct{})
	targets := make([]string, 0, limit)
	add := func(target string) {
		if len(targets) >= limit {
			return
		}
		upperTarget := strings.ToUpper(target)
		if strings.Contains(upperTarget, "$INDEX_ALLOCATION") || strings.Contains(target, "::$") {
			return
		}
		target = strings.TrimSuffix(target, "/") + "/"
		if _, _, _, err := normalizeBitmapProfileTarget(target); err != nil {
			return
		}
		key := strings.ToLower(target)
		if _, exists := seen[key]; exists {
			return
		}
		seen[key] = struct{}{}
		targets = append(targets, target)
	}

	add(currentURL)
	for _, adsURL := range chain {
		add(stripIndexAllocation(adsURL))
	}
	directories := make([]string, 0, len(foundDirectories))
	for directory := range foundDirectories {
		directories = append(directories, directory)
	}
	sort.Strings(directories)
	for _, directory := range directories {
		add(currentURL + directory + "/")
	}
	return targets
}

// runAutoBitmapProfiles is deliberately gated and bounded. A host that does
// not expose the H40 capability baseline pays for one failed target only; a
// working host profiles at most six directories in --auto and 24 in --full.
// Exact custom-SFN guessing is not enabled here because an ordinary 8.3 LFN is
// indistinguishable from custom alternate metadata without an external pair.
func runAutoBitmapProfiles(hc *http.Client, st *httpStats, ac *attackConfig, currentURL string,
	chain []string, visited map[string]struct{}, unavailableOrigins map[string]struct{}) map[string]bool {
	highWater := make(map[string]bool)
	profiles := make([]bitmapProfileOutput, 0)
	for _, target := range autoBitmapTargets(currentURL, chain, ac.foundDirectories) {
		key := strings.ToLower(target)
		if _, exists := visited[key]; exists {
			continue
		}
		origin := originKey(target)
		if _, unavailable := unavailableOrigins[origin]; unavailable {
			continue
		}
		visited[key] = struct{}{}
		profile, err := probeBitmapProfileTarget(target, hc, st)
		if err != nil {
			log.WithFields(log.Fields{"url": target, "error": err}).Debug("Auto $BITMAP profile failed")
			continue
		}
		if profile.BaselineUnavailable {
			// Only the base H40 capability oracle failing poisons the whole origin.
			// A confirmed directory (index.Present) whose ::$BITMAP/:$I30:$BITMAP
			// follow-ups merely flaked stays OracleAvailable=false too, but must not
			// blacklist sibling directories on the same origin that could still
			// resolve cleanly — see the BaselineUnavailable doc comment.
			unavailableOrigins[origin] = struct{}{}
			log.WithField("origin", origin).Debug("H40 capability baseline unavailable; skipping auto $BITMAP profiles for origin")
			continue
		}
		if !profile.IndexAllocation {
			continue
		}
		profiles = append(profiles, profile)
		if profile.HistoricalHighWatermark {
			highWater[key] = true
		}
	}
	if len(profiles) > 0 {
		beginSection(ac)
		printHuman(color.HiCyanString("[BITMAP-HIGHWATER] %s", pluralCount(len(profiles), "directory", "directories")))
		for _, profile := range profiles {
			emitBitmapProfile(profile)
		}
	}
	return highWater
}
