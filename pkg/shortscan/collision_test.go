package shortscan

import (
	"io"
	"regexp"
	"strings"
	"testing"

	"github.com/thezakman/shortscan/pkg/shortutil"
)

// hashedAliasFor builds the checksummed 8.3 stem Windows would emit for a long
// name once its classic family is saturated: the first two sanitized-uppercase
// characters followed by the four-hex checksum of the whole name.
func hashedAliasFor(longName string) string {
	filename, extension := splitLongName(longName)
	_, filename83, _ := shortutil.Gen8dot3(filename, extension)
	prefix := filename83
	if len(prefix) > 2 {
		prefix = prefix[:2]
	}
	return prefix + shortutil.Checksum(longName)
}

func TestChecksumMaskReconstructsHashedAlias(t *testing.T) {
	previousArgs, previousRegex := args, checksumRegex
	defer func() { args, checksumRegex = previousArgs, previousRegex }()
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	args = arguments{
		ChecksumMasks:    []string{"App_Web_????.dll"},
		ChecksumAlphabet: "abcdefghijklmnopqrstuvwxyz0123456789",
		ChecksumLimit:    256,
	}

	const longName = "App_Web_ab12.dll"
	aliasStem := hashedAliasFor(longName) // e.g. AP<ck>
	br := baseRequest{url: "http://example.test/", file: aliasStem, tilde: "~1", ext: ".DLL"}

	candidates := checksumMaskCandidates(br)
	var found *filenameCandidate
	for i := range candidates {
		if strings.EqualFold(candidates[i].record.filename+candidates[i].record.extension, longName) {
			found = &candidates[i]
			break
		}
	}
	if found == nil {
		t.Fatalf("checksum-mask did not reconstruct %q from alias %q (%d candidates)", longName, aliasStem, len(candidates))
	}
	if found.matchType != "checksum-mask" {
		t.Fatalf("match type = %q, want checksum-mask", found.matchType)
	}
	if !strings.EqualFold(found.checksum, shortutil.Checksum(longName)) {
		t.Fatalf("candidate checksum = %q, want %q", found.checksum, shortutil.Checksum(longName))
	}
	// Every emitted candidate must be checksum-valid and share the alias extension.
	for _, candidate := range candidates {
		full := candidate.record.filename + candidate.record.extension
		if !strings.EqualFold(shortutil.Checksum(full), aliasStem[len(aliasStem)-4:]) {
			t.Fatalf("candidate %q has the wrong checksum", full)
		}
		if !strings.EqualFold(candidate.record.extension83, "DLL") {
			t.Fatalf("candidate %q escaped the alias extension", full)
		}
	}
}

func TestExpandMask(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()
	args = arguments{ChecksumMaxLength: 5}

	if got := expandMask("App_Web_????.dll", "abc"); len(got) != 1 || got[0] != "App_Web_????.dll" {
		t.Fatalf("a mask without '*' should pass through unchanged: %v", got)
	}
	if got := expandMask("App_Web_.dll", "abc"); got != nil {
		t.Fatalf("a mask with no '?' or '*' must yield nothing: %v", got)
	}
	got := expandMask("App_Web_*.dll", "abcdefghijklmnopqrstuvwxyz0123456789")
	if len(got) != 5 {
		t.Fatalf("expected 5 length expansions, got %d: %v", len(got), got)
	}
	if got[0] != "App_Web_?.dll" || got[4] != "App_Web_?????.dll" {
		t.Fatalf("unexpected '*' expansion: %v", got)
	}
	// A large alphabet must still stop at the leaf budget, not run away.
	args = arguments{ChecksumMaxLength: 24}
	big := expandMask("App_Web_*.dll", "abcdefghijklmnopqrstuvwxyz0123456789")
	if len(big) == 0 || len(big) >= 24 {
		t.Fatalf("budget did not bound the '*' expansion: %d lengths", len(big))
	}
}

// TestChecksumMaskStarFindsLengthAutomatically proves the usability win: the
// operator writes 'App_Web_*.dll' and the tool discovers the real 4-character
// tail by iterating lengths, without being told the count of '?'.
func TestChecksumMaskStarFindsLengthAutomatically(t *testing.T) {
	previousArgs, previousRegex := args, checksumRegex
	defer func() { args, checksumRegex = previousArgs, previousRegex }()
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	args = arguments{
		ChecksumMasks:     []string{"App_Web_*.dll"},
		ChecksumAlphabet:  "abcdefghijklmnopqrstuvwxyz0123456789",
		ChecksumLimit:     4096,
		ChecksumMaxLength: 6,
	}
	const longName = "App_Web_ab12.dll" // 4-char tail; the mask never states 4
	br := baseRequest{url: "http://example.test/", file: hashedAliasFor(longName), tilde: "~1", ext: ".DLL"}
	found := false
	for _, c := range checksumMaskCandidates(br) {
		if strings.EqualFold(c.record.filename+c.record.extension, longName) {
			found = true
		}
	}
	if !found {
		t.Fatalf("variable-length '*' mask failed to discover %s", longName)
	}
}

func TestChecksumMaskIgnoresClassicAlias(t *testing.T) {
	previousArgs, previousRegex := args, checksumRegex
	defer func() { args, checksumRegex = previousArgs, previousRegex }()
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	args = arguments{
		ChecksumMasks:    []string{"Default?.aspx"},
		ChecksumAlphabet: "0123456789",
		ChecksumLimit:    256,
	}
	// DEFAUL is a classic six-character stem, not a PPHHHH hashed alias, so the
	// mask engine must not fire for it.
	br := baseRequest{url: "http://example.test/", file: "DEFAUL", tilde: "~1", ext: ".ASP"}
	if candidates := checksumMaskCandidates(br); len(candidates) != 0 {
		t.Fatalf("checksum-mask fired on a classic alias: %+v", candidates)
	}
}

func observedAlias(file, tilde, ext string) baseRequest {
	return baseRequest{url: "http://example.test/", file: file, tilde: tilde, ext: ext}
}

func TestSaturatedFamiliesRequireAllFourOrdinals(t *testing.T) {
	aliases := []baseRequest{
		observedAlias("PRIMAX", "~1", ""),
		observedAlias("PRIMAX", "~2", ""),
		observedAlias("PRIMAX", "~3", ""),
		observedAlias("PRIMAX", "~4", ""),
		observedAlias("ENTITY", "~1", ""), // not saturated
		observedAlias("ENTITY", "~2", ""),
	}
	families := saturatedFamilies(aliases)
	if len(families) != 1 || families[0].stem != "PRIMAX" {
		t.Fatalf("saturated families = %+v, want a single PRIMAX family", families)
	}

	checksum := shortutil.Checksum("PRIMAX5145")
	aliasStem := "PR" + checksum
	linked := familiesForAlias(families, "PR", "")
	if len(linked) != 1 || linked[0].stem != "PRIMAX" {
		t.Fatalf("familiesForAlias(%q) = %+v, want PRIMAX", aliasStem, linked)
	}
	// A different two-character prefix must not link to the PRIMAX family.
	if linked := familiesForAlias(families, "ZZ", ""); len(linked) != 0 {
		t.Fatalf("unexpected ancestry link for ZZ prefix: %+v", linked)
	}
}

func TestCollisionAncestryCandidatesRequireFamilyPrefixAndChecksum(t *testing.T) {
	previousArgs, previousRegex := args, checksumRegex
	defer func() { args, checksumRegex = previousArgs, previousRegex }()
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	args = arguments{CollisionAncestry: true}

	// A wordlist holding the true ancestor and two decoys with the same PRIMAX
	// prefix but different checksums.
	wc := newWordlistConfig([]wordlistSource{{
		name: "words",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("PRIMAX5145\nPRIMAX0000\nPRODUCT9\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	ac := &attackConfig{wordlist: wc}

	checksum := shortutil.Checksum("PRIMAX5145")
	families := []collisionFamily{{stem: "PRIMAX", ext: "", ordinals: map[int]struct{}{1: {}, 2: {}, 3: {}, 4: {}}}}
	br := observedAlias("PR"+checksum, "~1", "")

	candidates := collisionAncestryCandidates(ac, br, families)
	if len(candidates) != 1 {
		t.Fatalf("got %d ancestry candidates, want exactly PRIMAX5145: %+v", len(candidates), candidates)
	}
	candidate := candidates[0]
	if candidate.record.filename != "PRIMAX5145" || candidate.matchType != "collision-ancestry" {
		t.Fatalf("unexpected candidate: %+v", candidate)
	}
	if !strings.EqualFold(candidate.checksum, checksum) {
		t.Fatalf("candidate checksum = %q, want %q", candidate.checksum, checksum)
	}
	if len(candidate.families) != 1 || candidate.families[0] != "PRIMAX~*" {
		t.Fatalf("candidate families = %v, want [PRIMAX~*]", candidate.families)
	}

	// Without a saturated family there is no ancestry to propose.
	if candidates := collisionAncestryCandidates(ac, br, nil); len(candidates) != 0 {
		t.Fatalf("ancestry proposed without a saturated family: %+v", candidates)
	}
}
