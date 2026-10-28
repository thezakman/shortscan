package hashrecover

import (
	"strings"
	"testing"

	"github.com/thezakman/shortscan/pkg/shortutil"
)

func contains(values []string, wanted string) bool {
	for _, value := range values {
		if value == wanted {
			return true
		}
	}
	return false
}

func TestInverseStatesContainsKnownPolynomialState(t *testing.T) {
	const name = "a.txt3"
	checksum := shortutil.Checksum(name)
	if checksum != "EE90" {
		t.Fatalf("fixture checksum = %s, want EE90", checksum)
	}
	states, err := InverseStates(checksum)
	if err != nil {
		t.Fatal(err)
	}
	state := PolynomialState(name)
	found := false
	for _, candidate := range states {
		if candidate == state {
			found = true
			break
		}
	}
	if !found {
		t.Fatalf("polynomial state %04X absent from inverse set %v", state, states)
	}
}

func TestRecoverOneDigitTomGalvinFixture(t *testing.T) {
	matches, stats, err := RecoverMask("a.txt?", "0123456789", "EE90", 100)
	if err != nil {
		t.Fatal(err)
	}
	if !contains(matches, "a.txt3") {
		t.Fatalf("known filename absent: matches=%v stats=%+v", matches, stats)
	}
	for _, match := range matches {
		if got := shortutil.Checksum(match); got != "EE90" {
			t.Fatalf("%q has checksum %s", match, got)
		}
	}
}

func TestRecoverFourHexCharactersWithFixedContext(t *testing.T) {
	const name = "PR4A7C_BACKUP.config"
	checksum := shortutil.Checksum(name)
	matches, stats, err := RecoverMask("PR????_BACKUP.config", "0123456789ABCDEF", checksum, 100)
	if err != nil {
		t.Fatal(err)
	}
	if !contains(matches, name) {
		t.Fatalf("known filename absent: checksum=%s matches=%v stats=%+v", checksum, matches, stats)
	}
	if stats.ForwardLeaves != 256 {
		t.Fatalf("forward leaves = %d, want 256", stats.ForwardLeaves)
	}
	if stats.BackwardLeaves == 0 || stats.BackwardLeaves > 1024 {
		t.Fatalf("unexpected backward leaves: %+v", stats)
	}
	for _, match := range matches {
		if !strings.HasPrefix(match, "PR") || !strings.HasSuffix(match, "_BACKUP.config") {
			t.Fatalf("match escaped fixed grammar: %q", match)
		}
	}
}

// TestRecoverAppWebAssembly exercises the realistic win: reconstructing an
// ASP.NET dynamically-compiled assembly name (App_Web_<random>.dll) — a
// directory that is collision-saturated by construction, so its aliases are
// always hashed — from the checksum embedded in its hashed 8.3 alias. With a
// bounded random tail the checksum reduces ~1.7M grammar strings to a few dozen
// candidates that the caller then confirms over HTTP.
func TestRecoverAppWebAssembly(t *testing.T) {
	const name = "App_Web_ab12.dll"
	checksum := shortutil.Checksum(name)
	matches, stats, err := RecoverMask("App_Web_????.dll", "abcdefghijklmnopqrstuvwxyz0123456789", checksum, 4096)
	if err != nil {
		t.Fatal(err)
	}
	if !contains(matches, name) {
		t.Fatalf("known App_Web_ assembly absent: checksum=%s matches=%d", checksum, len(matches))
	}
	// 36^4 = 1,679,616 grammar strings collapse to O(hundreds) under one 16-bit
	// checksum. Assert a large reduction without pinning an exact count.
	if len(matches) > 500 {
		t.Fatalf("checksum reduced too weakly: %d survivors (stats=%+v)", len(matches), stats)
	}
	for _, match := range matches {
		if got := shortutil.Checksum(match); !strings.EqualFold(got, checksum) {
			t.Fatalf("%q has checksum %s, want %s", match, got, checksum)
		}
	}
}

// TestHighEntropyTailIsAmbiguous documents the honest limit: an 8-character
// random tail over a 36-char alphabet leaves ~2.5M checksum-valid candidates, so
// the checksum alone cannot pick the name — the search truncates at the limit.
// The checksum only becomes decisive once a grammar/wordlist narrows the tail.
func TestHighEntropyTailIsAmbiguous(t *testing.T) {
	const name = "App_Web_qz3k9f2p.dll"
	checksum := shortutil.Checksum(name)
	matches, stats, err := RecoverMask("App_Web_????????.dll", "abcdefghijklmnopqrstuvwxyz0123456789", checksum, 4096)
	if err != nil {
		t.Fatal(err)
	}
	if !stats.Truncated || len(matches) < 4096 {
		t.Fatalf("expected an ambiguous, truncated search for a high-entropy tail: matches=%d stats=%+v", len(matches), stats)
	}
}

func TestRejectsInvalidInputs(t *testing.T) {
	if _, _, err := RecoverMask("A?", "", "ABCD", 10); err == nil {
		t.Fatal("empty alphabet accepted")
	}
	if _, _, err := RecoverMask("A?", "ABC", "XYZ", 10); err == nil {
		t.Fatal("invalid checksum accepted")
	}
	if _, _, err := RecoverMask("A?", "ABC", "ABCD", 0); err == nil {
		t.Fatal("zero limit accepted")
	}
	if _, _, err := RecoverMask("ABC.def", "ABC", "ABCD", 10); err == nil {
		t.Fatal("mask without a placeholder accepted")
	}
}

// TestRejectsSupplementaryPlaneCharacters guards against silently searching with a
// model that can never find a match: the polynomial walk steps once per Go rune,
// but a supplementary-plane character (outside the BMP) encodes to a UTF-16
// surrogate PAIR in shortutil.Checksum, i.e. two steps. Before this validation,
// RecoverMask("?", "\U0001F600", checksum, N) silently returned zero matches for
// any checksum, including the real checksum of "\U0001F600" itself, with no
// indication the search was structurally incapable of finding it.
func TestRejectsSupplementaryPlaneCharacters(t *testing.T) {
	const emoji = "\U0001F600" // outside the Basic Multilingual Plane
	if _, _, err := RecoverMask("?", emoji, "ABCD", 10); err == nil {
		t.Fatal("supplementary-plane alphabet character accepted")
	}
	if _, _, err := RecoverMask(emoji+"?", "A", "ABCD", 10); err == nil {
		t.Fatal("supplementary-plane mask character accepted")
	}
}

func TestRejectsOversizedMask(t *testing.T) {
	// 10 unknowns over a 36-char alphabet is 36^5 backward leaves (~60M), which
	// must be refused by the default budget rather than allocating.
	_, _, err := RecoverMask("??????????.dll", "abcdefghijklmnopqrstuvwxyz0123456789", "ABCD", 10)
	if err == nil {
		t.Fatal("oversized mask accepted; expected a budget error")
	}
	if !strings.Contains(err.Error(), "too large") {
		t.Fatalf("unexpected error for oversized mask: %v", err)
	}
}

func TestEstimateLeaves(t *testing.T) {
	forward, backward := EstimateLeaves("PR????_BACKUP.config", "0123456789ABCDEF")
	if forward != 256 || backward != 256 {
		t.Fatalf("estimate = (%d,%d), want (256,256)", forward, backward)
	}
	// Odd unknown count splits with the larger half on the backward walk.
	forward, backward = EstimateLeaves("a.txt???", "0123456789")
	if forward != 10 || backward != 100 {
		t.Fatalf("odd estimate = (%d,%d), want (10,100)", forward, backward)
	}
}

func TestChecksumSpaceAccounting(t *testing.T) {
	stats := ChecksumSpaceStats()
	if stats.DistinctOutputs+stats.UnreachableOutputs != 1<<16 {
		t.Fatalf("checksum space does not total 2^16: %+v", stats)
	}
	states := 0
	for preimages, outputs := range stats.PreimageHistogram {
		states += preimages * outputs
	}
	if states != 1<<16 {
		t.Fatalf("preimage histogram accounts for %d states: %+v", states, stats)
	}
	if stats.MaxPreimages < 2 {
		t.Fatalf("expected non-bijective final mixing: %+v", stats)
	}
}
