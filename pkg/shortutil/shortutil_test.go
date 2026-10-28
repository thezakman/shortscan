package shortutil

import (
	"fmt"
	"strings"
	"testing"
	"unicode/utf8"
)

// --variants=false must still emit the word's own checksum (regression: it used to
// emit an EMPTY checksum, silently disabling collision-mode matching for that
// rainbow). --variants=true adds the case-folded forms on top.
func TestChecksumWordsAlwaysEmitsBaseChecksum(t *testing.T) {
	const word = "AdministratorConsole.aspx"

	off := ChecksumWords(strings.NewReader(word+"\n"), paramRegex, false)
	if len(off) != 1 {
		t.Fatalf("want 1 record, got %d", len(off))
	}
	if off[0].checksum == "" {
		t.Fatal("--variants=false emitted an empty checksum (would break collision-mode matching)")
	}
	if off[0].checksum != Checksum(word) {
		t.Errorf("--variants=false checksum = %q, want the word's own checksum %q", off[0].checksum, Checksum(word))
	}

	on := ChecksumWords(strings.NewReader(word+"\n"), paramRegex, true)
	if len(on[0].checksum) < len(off[0].checksum) {
		t.Errorf("--variants=true (%q) should be at least as long as --variants=false (%q)", on[0].checksum, off[0].checksum)
	}
	// The word's own checksum must be present among the variant chunks.
	if !strings.Contains(on[0].checksum, Checksum(word)) {
		t.Errorf("--variants=true checksum %q must contain the base checksum %q", on[0].checksum, Checksum(word))
	}

	// Deterministic: same input, byte-identical output.
	on2 := ChecksumWords(strings.NewReader(word+"\n"), paramRegex, true)
	if on[0].checksum != on2[0].checksum {
		t.Errorf("ChecksumWords not deterministic: %q vs %q", on[0].checksum, on2[0].checksum)
	}
}

// Modern checksum — golden values from the validated implementation.
func TestChecksum(t *testing.T) {
	cases := map[string]string{
		"index.html": "2EF5",
		"web.config": "F71C",
	}
	for in, want := range cases {
		if got := Checksum(in); got != want {
			t.Errorf("Checksum(%q) = %q, want %q", in, got, want)
		}
	}
}

// Checksum must process the input as UTF-16 code units, not Unicode code
// points — the reference C loops over a PWSTR. A character outside the
// Basic Multilingual Plane (e.g. an emoji) is a surrogate pair on real
// Windows/NTFS: two 16-bit units, so the checksum loop must run twice for
// it. Ranging over the Go string instead (one rune per iteration) would
// feed the loop one truncated 32-bit-down-to-16-bit value instead.
func TestChecksumNonBMPUsesSurrogatePair(t *testing.T) {
	viaSurrogates := Checksum("\U0001F600.txt") // manual UTF-16: D83D DE00 002E 0074 0078 0074

	// Reproduce the (wrong) rune-based loop this regression guards against,
	// to prove the fixed implementation no longer matches it.
	var ck uint16
	for _, c := range "\U0001F600.txt" {
		ck = ck*0x25 + uint16(c)
	}
	t2 := int32(ck) * 314159269
	if t2 < 0 {
		t2 = -t2
	}
	t2 -= int32(((uint64(t2) * uint64(1152921497)) >> 60) * uint64(1000000007))
	ck = uint16(t2)
	ck = (ck&0xf000)>>12 | (ck&0x0f00)>>4 | (ck&0x00f0)<<4 | (ck&0x000f)<<12
	viaRunes := fmt.Sprintf("%04X", ck)

	if viaSurrogates == viaRunes {
		t.Fatalf("Checksum on a non-BMP character matches the rune-based (wrong) computation: %q", viaSurrogates)
	}
}

// ChecksumOriginal must not panic on names shorter than two bytes (regression:
// f[0]/f[1] used to index out of range). The len>=2 path is unchanged.
func TestChecksumOriginalShortNames(t *testing.T) {
	for _, in := range []string{"", "a", ".", "ab", "abc"} {
		func() {
			defer func() {
				if r := recover(); r != nil {
					t.Errorf("ChecksumOriginal(%q) panicked: %v", in, r)
				}
			}()
			got := ChecksumOriginal(in)
			if len(got) != 4 {
				t.Errorf("ChecksumOriginal(%q) = %q, want 4 hex chars", in, got)
			}
		}()
	}
	if got := ChecksumOriginal("ab"); got != "2616" {
		t.Errorf("ChecksumOriginal(%q) = %q, want %q", "ab", got, "2616")
	}
}

func TestGen8dot3(t *testing.T) {
	cases := []struct {
		file, ext        string
		wantReq          bool
		wantF83, wantE83 string
	}{
		{"administrator", "aspx", true, "ADMINI", "ASP"}, // long base + long ext
		{"web", "config", true, "WEB", "CON"},            // long ext truncated
		{"index", "html", true, "INDEX", "HTM"},          // ext truncated
		{"login", "asp", false, "LOGIN", "ASP"},          // already 8.3-compliant
		{"report", "txt", false, "REPORT", "TXT"},        // 6+3, no short name
		// [MS-FSCC] 2.1.5.2.1: 8.3 names are ASCII-only; illegal (here,
		// non-ASCII) characters are deleted, not kept or replaced with '_'.
		{"ação", "txt", true, "AO", "TXT"},
	}
	for _, c := range cases {
		req, f83, e83 := Gen8dot3(c.file, c.ext)
		if req != c.wantReq || f83 != c.wantF83 || e83 != c.wantE83 {
			t.Errorf("Gen8dot3(%q,%q) = (%v,%q,%q), want (%v,%q,%q)",
				c.file, c.ext, req, f83, e83, c.wantReq, c.wantF83, c.wantE83)
		}
	}
}

// A non-ASCII character landing where the 6-byte truncation cuts must never
// leave a dangling UTF-8 continuation byte — stripNonASCII runs before
// truncation, so the truncated result is always pure ASCII.
func TestGen8dot3NonASCIINeverProducesInvalidUTF8(t *testing.T) {
	_, f83, e83 := Gen8dot3("abcdeçfgh", "txt")
	if !utf8.ValidString(f83) {
		t.Fatalf("f83 = %q is not valid UTF-8: %v", f83, []byte(f83))
	}
	if f83 != "ABCDEF" {
		t.Errorf("f83 = %q, want %q", f83, "ABCDEF")
	}
	if e83 != "TXT" {
		t.Errorf("e83 = %q, want %q", e83, "TXT")
	}
}
