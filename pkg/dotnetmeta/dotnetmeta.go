// Package dotnetmeta is a dependency-free reader for .NET (CLI/CLR) assembly
// metadata. Given the raw bytes of a managed PE — e.g. an App_Web_*.dll recovered
// by shortscan's cookieless source-disclosure chain — it extracts source-level
// content WITHOUT loading or executing the assembly:
//
//   - the CodeView PDB / build path (debug directory);
//   - the #Strings heap: every identifier name (namespaces, types, methods, fields,
//     control IDs, referenced-assembly names) — full application structure;
//   - the #US (user-strings) heap: every string LITERAL — for a compiled ASP.NET
//     page these are the WriteLiteral() arguments, i.e. the page's static HTML
//     markup, plus any hard-coded connection strings / secrets.
//
// It parses only the PE/CLI headers and the metadata heaps (no table-stream schema,
// no IL decode), which is enough to reconstruct most of a page's source surface and
// is robust against malformed input (every read is bounds-checked).
package dotnetmeta

import (
	"bytes"
	"debug/pe"
	"encoding/binary"
	"errors"
	"sort"
	"unicode/utf16"
	"unicode/utf8"
)

// Assembly holds what was recovered from a managed PE.
type Assembly struct {
	IsPE            bool     `json:"is_pe"`
	IsManaged       bool     `json:"is_managed"`
	PDBPath         string   `json:"pdb_path,omitempty"`
	MetadataVersion string   `json:"metadata_version,omitempty"`
	Names           []string `json:"names,omitempty"`    // #Strings heap
	Literals        []string `json:"literals,omitempty"` // #US heap
}

var errNotPE = errors.New("not a PE image")

// Inspect parses raw assembly bytes. It returns a best-effort *Assembly even on
// partial failure (e.g. PE-but-not-managed) and never panics on malformed input.
func Inspect(raw []byte) (*Assembly, error) {
	if len(raw) < 64 || raw[0] != 'M' || raw[1] != 'Z' {
		return nil, errNotPE
	}
	a := &Assembly{IsPE: true}
	f, err := pe.NewFile(bytes.NewReader(raw))
	if err != nil {
		return a, nil // MZ but unparseable header; caller can still string-scan
	}
	a.PDBPath = codeViewPDB(f, raw)

	// CLI header lives in DataDirectory[14] (COM descriptor).
	comRVA, _ := dataDir(f, 14)
	if comRVA == 0 {
		return a, nil // native PE, no managed metadata
	}
	comOff := rvaToOffset(f, comRVA)
	if comOff < 0 || comOff+16 > int64(len(raw)) {
		return a, nil
	}
	mdRVA := binary.LittleEndian.Uint32(raw[comOff+8 : comOff+12])
	mdOff := rvaToOffset(f, mdRVA)
	if mdOff < 0 {
		return a, nil
	}
	a.IsManaged = true
	parseMetadataRoot(raw, mdOff, a)
	return a, nil
}

func dataDir(f *pe.File, i int) (rva, size uint32) {
	switch oh := f.OptionalHeader.(type) {
	case *pe.OptionalHeader32:
		if i < len(oh.DataDirectory) {
			return oh.DataDirectory[i].VirtualAddress, oh.DataDirectory[i].Size
		}
	case *pe.OptionalHeader64:
		if i < len(oh.DataDirectory) {
			return oh.DataDirectory[i].VirtualAddress, oh.DataDirectory[i].Size
		}
	}
	return 0, 0
}

func rvaToOffset(f *pe.File, rva uint32) int64 {
	for _, s := range f.Sections {
		if rva >= s.VirtualAddress && rva < s.VirtualAddress+s.VirtualSize {
			return int64(s.Offset + (rva - s.VirtualAddress))
		}
	}
	return -1
}

// codeViewPDB reads the RSDS PDB path from the debug directory.
func codeViewPDB(f *pe.File, raw []byte) string {
	dd, size := dataDir(f, 6) // IMAGE_DIRECTORY_ENTRY_DEBUG
	if dd == 0 || size == 0 {
		return ""
	}
	off := rvaToOffset(f, dd)
	if off < 0 {
		return ""
	}
	for i := 0; i < int(size)/28; i++ {
		base := off + int64(i*28)
		if base+28 > int64(len(raw)) {
			break
		}
		e := raw[base:]
		if binary.LittleEndian.Uint32(e[12:16]) != 2 { // CODEVIEW
			continue
		}
		ptr := binary.LittleEndian.Uint32(e[24:28])
		if int64(ptr)+24 >= int64(len(raw)) {
			continue
		}
		cv := raw[ptr:]
		if len(cv) >= 24 && string(cv[0:4]) == "RSDS" {
			p := cv[24:]
			if n := bytes.IndexByte(p, 0); n >= 0 {
				return string(p[:n])
			}
		}
	}
	return ""
}

// parseMetadataRoot walks the metadata streams and fills Names/Literals.
func parseMetadataRoot(raw []byte, off int64, a *Assembly) {
	if off+20 > int64(len(raw)) || binary.LittleEndian.Uint32(raw[off:off+4]) != 0x424A5342 { // "BSJB"
		return
	}
	verLen := binary.LittleEndian.Uint32(raw[off+12 : off+16])
	if verLen > 255 || off+16+int64(verLen) > int64(len(raw)) {
		return
	}
	verBytes := raw[off+16 : off+16+int64(verLen)]
	if n := bytes.IndexByte(verBytes, 0); n >= 0 {
		verBytes = verBytes[:n]
	}
	a.MetadataVersion = string(verBytes)
	p := off + 16 + int64(align4(verLen)) // -> flags(2) + streams(2)
	if p+4 > int64(len(raw)) {
		return
	}
	nStreams := binary.LittleEndian.Uint16(raw[p+2 : p+4])
	p += 4
	for i := 0; i < int(nStreams) && p+8 <= int64(len(raw)); i++ {
		sOff := binary.LittleEndian.Uint32(raw[p : p+4])
		sSize := binary.LittleEndian.Uint32(raw[p+4 : p+8])
		nameStart := p + 8
		nameEnd := nameStart
		for nameEnd < int64(len(raw)) && raw[nameEnd] != 0 {
			nameEnd++
		}
		name := string(raw[nameStart:nameEnd])
		// stream name is null-terminated then padded to a 4-byte boundary
		p = nameStart + int64(align4(uint32(nameEnd-nameStart)+1))
		base := off + int64(sOff)
		end := base + int64(sSize)
		if base < 0 || end > int64(len(raw)) || base > end {
			continue
		}
		switch name {
		case "#Strings":
			a.Names = splitStrings(raw[base:end])
		case "#US":
			a.Literals = splitUserStrings(raw[base:end])
		}
	}
}

func align4(n uint32) uint32 { return (n + 3) &^ 3 }

// splitStrings walks the null-terminated UTF-8 #Strings heap into unique names.
func splitStrings(b []byte) []string {
	seen := map[string]struct{}{}
	var out []string
	start := 0
	for i := 0; i < len(b); i++ {
		if b[i] != 0 {
			continue
		}
		if i > start {
			s := string(b[start:i])
			if isPrintable(s) {
				if _, ok := seen[s]; !ok {
					seen[s] = struct{}{}
					out = append(out, s)
				}
			}
		}
		start = i + 1
	}
	sort.Strings(out)
	return out
}

// splitUserStrings walks the #US heap. Each entry is a compressed-length prefix
// followed by that many bytes of UTF-16LE plus one terminal flag byte.
func splitUserStrings(b []byte) []string {
	seen := map[string]struct{}{}
	var out []string
	i := 0
	if len(b) > 0 && b[0] == 0 {
		i = 1 // first entry is the empty string
	}
	for i < len(b) {
		l, n := readCompressedUint(b[i:])
		if n == 0 {
			break
		}
		i += n
		if l == 0 {
			continue
		}
		if i+int(l) > len(b) {
			break
		}
		blob := b[i : i+int(l)]
		i += int(l)
		// last byte is a flag; the UTF-16 payload is the rest (even length)
		u16 := blob
		if len(u16) > 0 {
			u16 = u16[:len(u16)-1]
		}
		if len(u16)%2 != 0 || len(u16) == 0 {
			continue
		}
		s := decodeUTF16(u16)
		if isPrintable(s) {
			if _, ok := seen[s]; !ok {
				seen[s] = struct{}{}
				out = append(out, s)
			}
		}
	}
	return out
}

// readCompressedUint decodes an ECMA-335 compressed unsigned integer.
func readCompressedUint(b []byte) (val uint32, n int) {
	if len(b) == 0 {
		return 0, 0
	}
	switch {
	case b[0]&0x80 == 0:
		return uint32(b[0]), 1
	case b[0]&0xC0 == 0x80:
		if len(b) < 2 {
			return 0, 0
		}
		return (uint32(b[0]&0x3F) << 8) | uint32(b[1]), 2
	case b[0]&0xE0 == 0xC0:
		if len(b) < 4 {
			return 0, 0
		}
		return (uint32(b[0]&0x1F) << 24) | (uint32(b[1]) << 16) | (uint32(b[2]) << 8) | uint32(b[3]), 4
	}
	return 0, 0
}

func decodeUTF16(b []byte) string {
	u := make([]uint16, len(b)/2)
	for i := range u {
		u[i] = binary.LittleEndian.Uint16(b[i*2:])
	}
	return string(utf16.Decode(u))
}

// isPrintable rejects heap junk: keep strings that are valid UTF-8 and mostly
// printable (allows tabs/newlines common in embedded HTML literals).
func isPrintable(s string) bool {
	if s == "" || !utf8.ValidString(s) {
		return false
	}
	bad := 0
	for _, r := range s {
		if r == '\t' || r == '\n' || r == '\r' {
			continue
		}
		if r < 0x20 || r == 0x7f {
			bad++
		}
	}
	return bad*4 < len(s)+1
}
