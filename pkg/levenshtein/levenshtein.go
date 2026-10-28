package levenshtein

import (
	"github.com/thezakman/shortscan/pkg/maths"
)

// Distance returns the Levenshtein edit distance for two strings
// Borrowed from: https://en.wikibooks.org/wiki/Algorithm_Implementation/Strings/Levenshtein_distance#Go
func Distance(a, b string) int {

	if a == b {
		return 0
	}
	left, right := []rune(a), []rune(b)
	for len(left) > 0 && len(right) > 0 && left[0] == right[0] {
		left, right = left[1:], right[1:]
	}
	for len(left) > 0 && len(right) > 0 && left[len(left)-1] == right[len(right)-1] {
		left, right = left[:len(left)-1], right[:len(right)-1]
	}
	if len(left) < len(right) {
		left, right = right, left
	}
	if len(right) == 0 {
		return len(left)
	}
	f := make([]int, len(right)+1)

	for j := range f {
		f[j] = j
	}

	for _, ca := range left {
		j := 1
		fj1 := f[0]
		f[0]++
		for _, cb := range right {
			mn := maths.Min(f[j]+1, f[j-1]+1)
			if cb != ca {
				mn = maths.Min(mn, fj1+1)
			} else {
				mn = maths.Min(mn, fj1)
			}

			fj1, f[j] = f[j], mn
			j++
		}
	}

	return f[len(f)-1]

}
