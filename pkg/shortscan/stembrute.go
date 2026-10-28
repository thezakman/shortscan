package shortscan

import (
	"fmt"
	"net/http"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/fatih/color"
	log "github.com/sirupsen/logrus"
	"github.com/thezakman/shortscan/pkg/shortutil"
)

// parseBruteRange parses the --brute-range value into an inclusive [lo, hi]
// completion-length range. Accepts "MIN-MAX" or "MIN,MAX" (e.g. "1-3"), or a
// bare "N" meaning 1..N. Ordering and positivity are enforced here; the caller
// enforces the 1..4 ceiling.
func parseBruteRange(s string) (int, int, error) {
	s = strings.TrimSpace(s)
	if s == "" {
		return 0, 0, fmt.Errorf("must not be empty")
	}
	lo, hi := 1, 0
	if sep := strings.IndexAny(s, "-,"); sep >= 0 {
		a, err1 := strconv.Atoi(strings.TrimSpace(s[:sep]))
		b, err2 := strconv.Atoi(strings.TrimSpace(s[sep+1:]))
		if err1 != nil || err2 != nil {
			return 0, 0, fmt.Errorf("%q is not a valid MIN-MAX range", s)
		}
		lo, hi = a, b
	} else {
		n, err := strconv.Atoi(s)
		if err != nil {
			return 0, 0, fmt.Errorf("%q is not a number or MIN-MAX range", s)
		}
		lo, hi = 1, n // a bare N is the range 1..N
	}
	// Positivity and ordering are enforced uniformly for both forms, so "0"
	// (bare -> 1..0) and "0-0" are rejected the same way instead of one slipping
	// through as an empty range that silently disables brute.
	if lo < 1 {
		return 0, 0, fmt.Errorf("%q: range min must be at least 1", s)
	}
	if lo > hi {
		return 0, 0, fmt.Errorf("%q: range min %d is greater than max %d", s, lo, hi)
	}
	return lo, hi, nil
}

// defaultBruteRange is the mode-dependent --brute-range applied when the user
// did not set one explicitly: --full digs one level deeper (1-3) than --auto or
// a bare --brute (1-2).
func defaultBruteRange(full bool) string {
	if full {
		return "1-3"
	}
	return "1-2"
}

// stemBruteExtensions returns every real extension whose 8.3 form matches the
// observed short extension: the short extension itself, plus every entry in
// wellKnownExtensions that truncates to the same three letters. The 8.3
// extension is genuinely ambiguous past three characters — ASP matches both
// .asp and .aspx — so a brute candidate must be tried against all of them,
// not just the literal short extension.
func stemBruteExtensions(shortExt string) []string {
	if shortExt == "" {
		return []string{""}
	}
	// Dedup key is the dot-stripped, lower-cased extension so the seed short
	// extension ("asp") and a dotted well-known entry (".asp") collapse to the
	// same key — otherwise the observed extension is emitted twice (once as the
	// seed, once from wellKnownExtensions), wasting an HTTP verification per group.
	norm := func(e string) string { return strings.TrimPrefix(strings.ToLower(e), ".") }
	seen := map[string]struct{}{norm(shortExt): {}}
	out := []string{"." + norm(shortExt)}
	for _, extension := range wellKnownExtensions {
		_, _, extension83 := shortutil.Gen8dot3("x", extension)
		if !strings.EqualFold(extension83, shortExt) {
			continue
		}
		key := norm(extension)
		if _, exists := seen[key]; exists {
			continue
		}
		seen[key] = struct{}{}
		out = append(out, extension)
	}
	return out
}

// bruteStemSuffixes returns alphabet completions of length lo..hi, ordered
// shortest-first: a short completion (a plural "s", a single digit) is both far
// more likely and far cheaper to prove than a long one, so trying them in that
// order keeps the request count small even when hi is raised. lengths below lo
// are still built (they are the prefixes the longer ones extend) but not emitted,
// so a range like 2-3 skips the single-char completions entirely.
//
// Emission is capped at maxCount. Without it the set size is charset^hi, which is
// unbounded by the charset length and reaches tens of millions (OOM) for a large
// --brute-charset at hi=4 — even though the caller can never spend more than its
// --brute-limit of them. Passing that limit as maxCount keeps peak memory bounded
// to the request budget while preserving the shortest-first order.
func bruteStemSuffixes(alphabet string, lo, hi, maxCount int) []string {
	chars := strings.Split(alphabet, "")
	if maxCount <= 0 {
		return nil
	}
	var out []string
	current := []string{""}
	for length := 1; length <= hi; length++ {
		next := make([]string, 0, len(current)*len(chars))
		for _, prefix := range current {
			for _, c := range chars {
				s := prefix + c
				next = append(next, s)
				if length >= lo {
					out = append(out, s)
					if len(out) >= maxCount {
						return out
					}
				}
			}
		}
		current = next
	}
	return out
}

// stemAlreadyResolved reports whether some already-recovered long name in this
// directory already 8.3-shortens to this alias's (stem, extension) — meaning an
// earlier, cheaper technique (wordlist, sibling, references, collision-ancestry,
// webdav, tilde-continuation) already answered it, so brute has nothing
// left to prove here and should not spend its request budget on it.
func stemAlreadyResolved(ac *attackConfig, br baseRequest) bool {
	stem := strings.ToUpper(br.file)
	shortExt := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
	ac.autocompleteMutex.Lock()
	defer ac.autocompleteMutex.Unlock()
	for path := range ac.foundFiles {
		filename, extension := splitLongName(path)
		if filename == "" {
			continue
		}
		_, filename83, extension83 := shortutil.Gen8dot3(filename, extension)
		if strings.EqualFold(filename83, stem) && strings.EqualFold(extension83, shortExt) {
			return true
		}
	}
	return false
}

// recoverStemBruteAliases is the last-resort recovery pass: for every classic
// (non-checksummed) short-name alias that survived every earlier technique still
// unresolved, guess the invisible tail of its long name directly over HTTP. The
// 8.3 tilde-matching oracle can only ever prove the first six stem characters and
// the first three extension characters — past that boundary there is no wildcard
// query that observes more (live-calibrated), so the only way to learn character
// 7+ is to propose a candidate and check whether it exists. Bounded by
// --brute-range / --brute-limit so it stays a short, opt-in brute
// rather than an unbounded one. Deterministic second pass, run after the
// concurrent enumerate() workers finish, mirroring sibling/collision-ancestry
// recovery.
func recoverStemBruteAliases(hc *http.Client, st *httpStats, ac *attackConfig, timedOut func() bool) int {
	if !args.Brute || ac == nil || ac.autocomplete == "none" {
		return 0
	}
	lo, hi, err := parseBruteRange(args.BruteRange)
	if err != nil {
		lo, hi = 1, 2 // cli already validated; defensive fallback to the default range
	}
	limit := args.BruteLimit
	if limit <= 0 {
		limit = 2000
	}
	alphabet := args.BruteCharset
	if alphabet == "" {
		alphabet = "abcdefghijklmnopqrstuvwxyz0123456789"
	}
	// Cap generation at the request budget: the loop below can never send more
	// than `limit` probes, so building more than `limit` completions is wasted
	// work and, at hi=4 with a large charset, an OOM risk.
	suffixes := bruteStemSuffixes(alphabet, lo, hi, limit)
	method := autocompleteProbeMethod(ac.autocomplete)

	seen := make(map[string]struct{})
	var groups []baseRequest
	for _, br := range observedRecoveryAliases(ac) {
		if br.file == "" {
			continue
		}
		if _, _, hashed := hashedAliasFields(br.file); hashed {
			// Checksummed aliases already have a cheap, exact oracle
			// (--checksum-mask / --collision-ancestry) — raw character brute
			// buys nothing there and would just waste the request budget.
			continue
		}
		key := strings.ToLower(br.url) + "\x00" + strings.ToUpper(br.file) + "\x00" + strings.ToUpper(br.ext)
		if _, exists := seen[key]; exists {
			continue
		}
		seen[key] = struct{}{}
		if stemAlreadyResolved(ac, br) {
			continue
		}
		groups = append(groups, br)
	}

	var recovered, requests, groupsStarted int64
	var budgetExhausted int32
	var linesMu sync.Mutex
	var lines []string

	// Groups are independent of each other — different unresolved short names, no
	// shared per-group state — but --brute-limit is a single TOTAL budget across all
	// of them (not per group), so unlike the plain per-alias parallelism in
	// sibling/collision-ancestry/references, this needs a shared atomic counter plus
	// a shared "stop starting new work" flag, checked both before a group begins and
	// before every request within it, to keep honouring the budget under concurrency.
	concurrency := args.Concurrency
	if concurrency < 1 {
		concurrency = 1 // an unset -c (e.g. a hand-built arguments{} in tests) must not deadlock a 0-buffered channel
	}
	sem := make(chan struct{}, concurrency)
	wg := new(sync.WaitGroup)
	for _, br := range groups {
		// --maxtime soft budget, checked between groups — see sibling.go's
		// recoverSiblingAliases for the fuller rationale.
		if timedOut != nil && timedOut() {
			break
		}
		br := br
		wg.Add(1)
		go func() {
			sem <- struct{}{}
			defer func() { <-sem; wg.Done() }()
			if atomic.LoadInt32(&budgetExhausted) != 0 {
				// Budget was already gone before this goroutine got a worker slot;
				// don't count it as started so the "groups left unbruted" count below
				// stays honest.
				return
			}
			atomic.AddInt64(&groupsStarted, 1)
			stem := strings.ToUpper(br.file)
			shortExt := strings.TrimPrefix(strings.ToUpper(br.ext), ".")
			baseURL := recoveryBaseURL(br)
			extensions := stemBruteExtensions(shortExt)
		suffixLoop:
			for _, suffix := range suffixes {
				for _, extension := range extensions {
					if atomic.LoadInt32(&budgetExhausted) != 0 {
						break suffixLoop
					}
					// The observed short name only ever proves the stem uppercased —
					// it carries no signal about the real casing beyond it. Present
					// (and request) the guess all-lowercase, the common convention on
					// disk; resolution itself is case-insensitive either way.
					filename := strings.ToLower(stem) + suffix
					_, filename83, extension83 := shortutil.Gen8dot3(filename, extension)
					if !strings.EqualFold(filename83, stem) || !strings.EqualFold(extension83, shortExt) {
						// Gen8dot3 rejected this (suffix, extension) pairing before it
						// could ever generate an HTTP request — must not consume budget,
						// or a stem shorter than 6 chars (every suffix 8.3-truncates to
						// something else) burns the whole --brute-limit on combinations
						// that were never going to be probed, starving every other group.
						continue
					}
					candidatePath := pathEscape(filename + extension)
					candidate := filenameCandidate{
						record: wordlistRecord{
							filename: filename, extension: extension,
							filename83: filename83, extension83: extension83,
						},
						matchType: "brute",
						source:    pluralCount(len(suffix), "extra char", "extra chars"),
					}
					ac.autocompleteMutex.Lock()
					if _, exists := ac.foundFiles[foundFileKey(candidatePath)]; exists {
						ac.autocompleteMutex.Unlock()
						continue
					}
					ac.autocompleteMutex.Unlock()

					if n := atomic.AddInt64(&requests, 1); n > int64(limit) {
						atomic.StoreInt32(&budgetExhausted, 1)
						break suffixLoop
					}

					res, matched, err := probeAutocompleteCandidate(hc, st, ac, br, baseURL, candidate)
					if err != nil {
						log.WithFields(log.Fields{"err": err, "method": method, "url": baseURL + candidatePath}).Info("Stem-brute check error")
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
						line := fmt.Sprintf("  %s -> %s (%s; %s; ordinal unverified; status %d)",
							group, color.HiGreenString(baseURL+candidatePath), candidate.source, profile, res.StatusCode)
						linesMu.Lock()
						lines = append(lines, line)
						linesMu.Unlock()
					} else {
						printJSON(resultOutput{
							Type: "recovery", FullMatch: true, BaseUrl: baseURL,
							File: br.file, Tilde: br.tilde, Ext: br.ext, Fullname: candidatePath,
							MatchType: "brute", Status: res.StatusCode,
							CollisionGroup: group, OrdinalVerified: boolPointer(candidateVerifiesOrdinal(br, candidatePath)),
							Oracle: ac.autocomplete, Method: method, DerivedFrom: candidate.source,
						})
					}
					break suffixLoop
				}
			}
		}()
	}
	wg.Wait()

	if len(lines) > 0 {
		beginSection(ac)
		printHuman(color.HiCyanString("[BRUTE] %s recovered", pluralCount(len(lines), "name", "names")))
		for _, line := range lines {
			printHuman(line)
		}
	}
	// No silent truncation: --brute-limit is a total budget for this whole
	// directory (not per group — a directory with many unresolved short names
	// would otherwise multiply the request volume by however many groups it
	// has), so say so when it cuts the pass off with groups still untried
	// instead of quietly reporting fewer recoveries than were actually possible.
	// groupsStarted undercounts slightly under concurrency (a goroutine that started
	// but got cut off mid-suffix-search still counts as "started", not "complete"),
	// so "remaining" here is a conservative lower bound, never an overclaim.
	if atomic.LoadInt32(&budgetExhausted) != 0 {
		remaining := len(groups) - int(atomic.LoadInt64(&groupsStarted))
		if remaining > 0 {
			// The human ⚠ below already says this; keep the log line at Debug so the
			// default output shows the truncation once, not twice.
			log.WithFields(log.Fields{"limit": limit, "groupsRemaining": remaining}).Debug("brute request budget exhausted; groups left unbruted")
			printHuman(color.HiYellowString("⚠ --brute-limit (%d) reached — %s left unbruted in this directory (raise --brute-limit to try more)", limit, pluralCount(remaining, "short-name group", "short-name groups")))
		}
	}
	return int(recovered)
}
