package dotnetmeta

import (
	"encoding/binary"
	"testing"
	"unicode/utf16"
)

func TestReadCompressedUint(t *testing.T) {
	cases := []struct {
		in  []byte
		val uint32
		n   int
	}{
		{[]byte{0x03}, 3, 1},
		{[]byte{0x7f}, 0x7f, 1},
		{[]byte{0x80, 0x80}, 0x80, 2},   // 2-byte form
		{[]byte{0xAE, 0x57}, 0x2E57, 2}, // 0x80|0x2E, 0x57
		{[]byte{0xC0, 0x00, 0x40, 0x00}, 0x4000, 4},
		{[]byte{}, 0, 0},
	}
	for _, c := range cases {
		v, n := readCompressedUint(c.in)
		if v != c.val || n != c.n {
			t.Fatalf("readCompressedUint(%v) = (%d,%d), want (%d,%d)", c.in, v, n, c.val, c.n)
		}
	}
}

func TestSplitStrings(t *testing.T) {
	heap := append([]byte{0}, []byte("Acme.Billing\x00Compute\x00\x00HardcodedConnString\x00")...)
	got := splitStrings(heap)
	want := map[string]bool{"Acme.Billing": false, "Compute": false, "HardcodedConnString": false}
	for _, s := range got {
		if _, ok := want[s]; ok {
			want[s] = true
		}
	}
	for s, seen := range want {
		if !seen {
			t.Fatalf("expected name %q in %v", s, got)
		}
	}
}

func TestSplitUserStrings(t *testing.T) {
	// build a #US heap with one literal: the classic hard-coded connection string
	lit := "Server=db;Pwd=secret!"
	u16 := utf16.Encode([]rune(lit))
	payload := make([]byte, len(u16)*2+1) // UTF-16LE + 1 flag byte
	for i, c := range u16 {
		binary.LittleEndian.PutUint16(payload[i*2:], c)
	}
	heap := append([]byte{0}, byte(len(payload))) // 1-byte compressed length (len < 0x80)
	heap = append(heap, payload...)
	got := splitUserStrings(heap)
	if len(got) != 1 || got[0] != lit {
		t.Fatalf("splitUserStrings recovered %v, want [%q]", got, lit)
	}
}

func TestInspectNonPE(t *testing.T) {
	if _, err := Inspect([]byte("not a pe at all")); err == nil {
		t.Fatalf("Inspect must reject non-PE input")
	}
}

func TestIsPrintable(t *testing.T) {
	if !isPrintable("Acme.Internal.Billing") {
		t.Fatalf("identifier must be printable")
	}
	if !isPrintable("<div class=\"x\">\r\n hi") { // HTML literal with whitespace
		t.Fatalf("HTML literal must be printable")
	}
	if isPrintable("\x01\x02\x03\x04\x05") {
		t.Fatalf("control-byte junk must be rejected")
	}
}

func TestParseMetadataRootNoPanicOnTruncation(t *testing.T) {
	// BSJB signature + a version length (200) far larger than the buffer.
	// Before the bounds fix this panicked slicing the version string.
	raw := make([]byte, 20)
	binary.LittleEndian.PutUint32(raw[0:], 0x424A5342) // "BSJB"
	binary.LittleEndian.PutUint32(raw[12:], 200)       // verLen way past end
	a := &Assembly{}
	parseMetadataRoot(raw, 0, a) // must not panic
	if a.MetadataVersion != "" {
		t.Fatalf("truncated version must not be parsed, got %q", a.MetadataVersion)
	}
}

func TestInspectNoPanicOnGarbage(t *testing.T) {
	// MZ-prefixed but otherwise random/truncated bytes must never panic.
	for _, b := range [][]byte{
		{'M', 'Z'},
		append([]byte("MZ"), make([]byte, 200)...),
		[]byte("MZ\x90\x00\x03\x00\x00\x00\x04\x00"),
	} {
		if _, err := Inspect(b); err != nil && err != errNotPE {
			t.Fatalf("unexpected error on garbage: %v", err)
		}
	}
}
