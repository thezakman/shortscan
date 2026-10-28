package levenshtein

import (
	"strings"
	"testing"
)

func TestDistance(t *testing.T) {
	for _, tc := range []struct {
		a, b string
		want int
	}{
		{"", "", 0}, {"", "世界", 2}, {"kitten", "sitting", 3},
		{"café", "cafe", 1}, {"prefix-suffix", "prefix-middle-suffix", 7},
		{"ab", "ba", 2}, {"identical", "identical", 0},
		{strings.Repeat("a", 4096) + "x" + strings.Repeat("b", 4096), strings.Repeat("a", 4096) + "y" + strings.Repeat("b", 4096), 1},
	} {
		if got := Distance(tc.a, tc.b); got != tc.want {
			t.Fatalf("distance=%d want=%d", got, tc.want)
		}
		if got := Distance(tc.b, tc.a); got != tc.want {
			t.Fatalf("reverse distance=%d want=%d", got, tc.want)
		}
	}
}

func BenchmarkSimilarResponses(b *testing.B) {
	left := strings.Repeat("response prefix ", 100) + "one" + strings.Repeat(" suffix", 100)
	right := strings.Repeat("response prefix ", 100) + "two" + strings.Repeat(" suffix", 100)
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		Distance(left, right)
	}
}
