// Package hashrecover performs constrained inversion of the four-hex checksum
// embedded in Windows collision-mode 8.3 aliases (the "PPHHHH~N" form).
//
// A 16-bit checksum does not uniquely identify a long filename, so this package
// is a candidate generator, not an oracle. Callers must constrain the candidate
// grammar with a mask and verify every surviving name with an independent HTTP
// oracle before treating it as a recovered filename.
//
// The checksum's pre-mixing state is a polynomial modulo 2^16 with an odd
// multiplier (37 = 0x25), so the state is invertible per character. That lets a
// fixed N-character mask be searched as two bounded alphabet^(N/2) halves joined
// on the 16-bit state (meet in the middle) rather than a single alphabet^N walk.
package hashrecover

import (
	"fmt"
	"math"
	"strconv"
	"strings"

	"github.com/thezakman/shortscan/pkg/shortutil"
)

const polynomialMultiplier uint16 = 0x25

// DefaultMaxForwardLeaves bounds the forward map (memory). DefaultMaxBackwardLeaves
// bounds the backward walk (time). Both are deliberately conservative; the CLI
// surfaces a clear error asking the operator to narrow the mask or alphabet
// rather than letting a large mask exhaust memory.
const (
	DefaultMaxForwardLeaves  = 8_000_000
	DefaultMaxBackwardLeaves = 64_000_000
)

// Stats describes the bounded search performed by RecoverMask.
type Stats struct {
	Unknowns       int
	InverseStates  int
	ForwardLeaves  uint64
	BackwardLeaves uint64
	Matches        int
	Truncated      bool
}

// SpaceStats describes the 16-bit post-mixing map used by the modern checksum.
type SpaceStats struct {
	DistinctOutputs    int
	UnreachableOutputs int
	MaxPreimages       int
	PreimageHistogram  map[int]int
}

// PolynomialState returns the 16-bit state produced before Windows applies the
// final checksum mixing and nibble reversal.
//
// BMP-only: this steps the polynomial once per Go rune (uint16(r)), matching
// shortutil.Checksum's utf16.Encode-based stepping only for characters in the
// Basic Multilingual Plane (code point <= 0xFFFF). A supplementary-plane rune
// (e.g. an emoji) encodes to a UTF-16 surrogate PAIR — two checksum steps, not
// one — so this function (and the RecoverMaskBudget search built on the same
// one-step-per-position model) cannot reproduce or search for the true checksum
// of a name containing one. RecoverMaskBudget rejects such input explicitly
// rather than silently searching a model that can never find a match.
func PolynomialState(name string) uint16 {
	var state uint16
	for _, r := range name {
		state = state*polynomialMultiplier + uint16(r)
	}
	return state
}

// checksumFromState mirrors the final mixing in shortutil.Checksum. Keeping it
// here lets the package enumerate every pre-mixing state for a displayed hash.
func checksumFromState(state uint16) uint16 {
	t := int32(math.Abs(float64(int32(state) * 314159269)))
	t -= int32(((uint64(t) * uint64(1152921497)) >> 60) * uint64(1000000007))
	checksum := uint16(t)
	return (checksum&0xf000)>>12 |
		(checksum&0x0f00)>>4 |
		(checksum&0x00f0)<<4 |
		(checksum&0x000f)<<12
}

// ParseChecksum validates a four-hex-digit checksum string.
func ParseChecksum(raw string) (uint16, error) {
	raw = strings.TrimSpace(raw)
	if len(raw) != 4 {
		return 0, fmt.Errorf("checksum must contain exactly four hexadecimal digits")
	}
	value, err := strconv.ParseUint(raw, 16, 16)
	if err != nil {
		return 0, fmt.Errorf("invalid checksum %q: %w", raw, err)
	}
	return uint16(value), nil
}

// InverseStates returns every 16-bit polynomial state that maps to the displayed
// four-hex checksum. The final Windows mixing is not a permutation, so a real
// checksum may have one, two or three pre-mixing states.
func InverseStates(checksum string) ([]uint16, error) {
	target, err := ParseChecksum(checksum)
	if err != nil {
		return nil, err
	}
	states := make([]uint16, 0, 2)
	for value := 0; value <= math.MaxUint16; value++ {
		state := uint16(value)
		if checksumFromState(state) == target {
			states = append(states, state)
		}
	}
	return states, nil
}

// ChecksumSpaceStats measures how many polynomial states reach each displayed
// checksum. Useful when estimating candidate reduction: the final mixing is not
// a permutation, so a real checksum may have more than one state.
func ChecksumSpaceStats() SpaceStats {
	counts := make([]int, math.MaxUint16+1)
	for value := 0; value <= math.MaxUint16; value++ {
		counts[checksumFromState(uint16(value))]++
	}
	stats := SpaceStats{PreimageHistogram: make(map[int]int)}
	for _, count := range counts {
		stats.PreimageHistogram[count]++
		if count == 0 {
			stats.UnreachableOutputs++
			continue
		}
		stats.DistinctOutputs++
		if count > stats.MaxPreimages {
			stats.MaxPreimages = count
		}
	}
	return stats
}

func uniqueRunes(raw string) []rune {
	seen := make(map[rune]struct{})
	result := make([]rune, 0, len(raw))
	for _, r := range raw {
		if _, exists := seen[r]; exists {
			continue
		}
		seen[r] = struct{}{}
		result = append(result, r)
	}
	return result
}

func inverseOdd16(value uint16) uint16 {
	// Newton iteration in Z/(2^16); each round doubles the number of correct low
	// bits for an odd input.
	x := value
	for i := 0; i < 4; i++ {
		x *= 2 - value*x
	}
	return x
}

var inversePolynomialMultiplier = inverseOdd16(polynomialMultiplier)

func reverseStep(state uint16, r rune) uint16 {
	return (state - uint16(r)) * inversePolynomialMultiplier
}

// powSaturate returns base^exp saturated at math.MaxUint64 to avoid overflow
// when estimating a mask's search size.
func powSaturate(base, exp uint64) uint64 {
	result := uint64(1)
	for i := uint64(0); i < exp; i++ {
		if base != 0 && result > math.MaxUint64/base {
			return math.MaxUint64
		}
		result *= base
	}
	return result
}

// EstimateLeaves returns the forward (memory) and backward (time) leaf counts a
// mask/alphabet would generate, saturating on overflow. It lets a caller reject
// an oversized search before allocating anything.
func EstimateLeaves(mask, alphabet string) (forward, backward uint64) {
	unknowns := uint64(strings.Count(mask, "?"))
	base := uint64(len(uniqueRunes(alphabet)))
	half := unknowns / 2
	return powSaturate(base, half), powSaturate(base, unknowns-half)
}

// RecoverMask finds strings matching mask whose Windows collision checksum equals
// checksum. A question mark denotes one character from alphabet; fixed mask
// characters (including a dot and extension) participate in the checksum. The
// result is truncated at limit and remains ambiguous whenever several candidate
// strings share the checksum.
func RecoverMask(mask, alphabet, checksum string, limit int) ([]string, Stats, error) {
	return RecoverMaskBudget(mask, alphabet, checksum, limit, DefaultMaxForwardLeaves, DefaultMaxBackwardLeaves)
}

// RecoverMaskBudget is RecoverMask with explicit leaf budgets. It errors instead
// of allocating when the mask/alphabet exceeds either budget.
func RecoverMaskBudget(mask, alphabet, checksum string, limit, maxForwardLeaves, maxBackwardLeaves int) ([]string, Stats, error) {
	var stats Stats
	if limit <= 0 {
		return nil, stats, fmt.Errorf("limit must be positive")
	}
	chars := uniqueRunes(alphabet)
	if len(chars) == 0 {
		return nil, stats, fmt.Errorf("alphabet must not be empty")
	}
	for _, r := range chars {
		if r > 0xFFFF {
			return nil, stats, fmt.Errorf("alphabet character %q is outside the Basic Multilingual Plane (encodes to a UTF-16 surrogate pair): this search steps one polynomial state per character and cannot represent it", r)
		}
	}
	positions := []rune(mask)
	for _, r := range positions {
		if r == '?' {
			stats.Unknowns++
		} else if r > 0xFFFF {
			return nil, stats, fmt.Errorf("mask character %q is outside the Basic Multilingual Plane (encodes to a UTF-16 surrogate pair): this search steps one polynomial state per character and cannot represent it", r)
		}
	}
	if stats.Unknowns == 0 {
		return nil, stats, fmt.Errorf("mask must contain at least one '?' placeholder")
	}
	forwardEstimate, backwardEstimate := EstimateLeaves(mask, alphabet)
	if maxForwardLeaves > 0 && forwardEstimate > uint64(maxForwardLeaves) {
		return nil, stats, fmt.Errorf("mask too large: forward search ~%d leaves exceeds budget %d; narrow the mask or alphabet", forwardEstimate, maxForwardLeaves)
	}
	if maxBackwardLeaves > 0 && backwardEstimate > uint64(maxBackwardLeaves) {
		return nil, stats, fmt.Errorf("mask too large: backward search ~%d leaves exceeds budget %d; narrow the mask or alphabet", backwardEstimate, maxBackwardLeaves)
	}
	targetStates, err := InverseStates(checksum)
	if err != nil {
		return nil, stats, err
	}
	stats.InverseStates = len(targetStates)
	if len(targetStates) == 0 {
		return nil, stats, nil
	}

	// Place the cut immediately after half of the unknown positions. Fixed
	// characters on either side fold into the corresponding traversal.
	half := stats.Unknowns / 2
	cut := 0
	seenUnknowns := 0
	if half > 0 {
		for i, r := range positions {
			if r == '?' {
				seenUnknowns++
			}
			if seenUnknowns == half {
				cut = i + 1
				break
			}
		}
	}

	working := append([]rune(nil), positions...)
	forward := make(map[uint16][]string)
	var walkForward func(int, uint16)
	walkForward = func(index int, state uint16) {
		if index == cut {
			stats.ForwardLeaves++
			prefixes := forward[state]
			if len(prefixes) < limit {
				forward[state] = append(prefixes, string(working[:cut]))
			} else {
				// A single intermediate state has more colliding prefixes than the
				// candidate cap. Dropping them keeps memory bounded, but a valid name
				// could be among the dropped prefixes, so surface the truncation
				// instead of reporting a complete result set.
				stats.Truncated = true
			}
			return
		}
		if positions[index] != '?' {
			working[index] = positions[index]
			walkForward(index+1, state*polynomialMultiplier+uint16(positions[index]))
			return
		}
		for _, r := range chars {
			working[index] = r
			walkForward(index+1, state*polynomialMultiplier+uint16(r))
		}
	}
	walkForward(0, 0)

	results := make([]string, 0)
	resultSet := make(map[string]struct{})
	stop := false
	var walkBackward func(int, uint16)
	walkBackward = func(index int, state uint16) {
		if stop {
			return
		}
		if index < cut {
			stats.BackwardLeaves++
			for _, prefix := range forward[state] {
				candidate := prefix + string(working[cut:])
				if _, exists := resultSet[candidate]; exists {
					continue
				}
				// Re-check with the canonical implementation to guard against any
				// mistake in the state inversion and to preserve exact semantics.
				if !strings.EqualFold(shortutil.Checksum(candidate), checksum) {
					continue
				}
				resultSet[candidate] = struct{}{}
				results = append(results, candidate)
				if len(results) >= limit {
					stats.Truncated = true
					stop = true
					return
				}
			}
			return
		}
		if positions[index] != '?' {
			working[index] = positions[index]
			walkBackward(index-1, reverseStep(state, positions[index]))
			return
		}
		for _, r := range chars {
			working[index] = r
			walkBackward(index-1, reverseStep(state, r))
			if stop {
				return
			}
		}
	}
	for _, targetState := range targetStates {
		walkBackward(len(positions)-1, targetState)
		if stop {
			break
		}
	}
	stats.Matches = len(results)
	return results, stats, nil
}
