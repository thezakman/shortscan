// ----------------------------------------------------
// Shortutil
// A short filename utility written by bitquark & TheZakMan
// ----------------------------------------------------
// Docs and code: https://github.com/thezakman/shortscan
// ----------------------------------------------------

package shortutil

import (
	"bufio"
	"fmt"
	"github.com/alexflint/go-arg"
	"github.com/fatih/color"
	"github.com/thezakman/shortscan/pkg/maths"
	"io"
	"log"
	"math"
	"net/url"
	"os"
	"path"
	"regexp"
	"sort"
	"strings"
	"unicode/utf16"
)

type wordlistRecord struct {
	checksum    string
	filename    string
	extension   string
	filename83  string
	extension83 string
}

// Command-line arguments
var args struct {
	Wordlist *struct {
		Filename string `arg:"positional,required" help:"wordlist to ingest"`
		KeepCase bool   `arg:"--keepcase" help:"keep the original case rather than upper-casing words" default:"false"`
		Uniq     bool   `arg:"--uniq" help:"allow only unique words" default:"true"`
		Variants bool   `arg:"--variants" help:"generate checksums for case variants of input words (e.g. ping.aspx, Ping.aspx, PING.ASPX)" default:"true"`
	} `arg:"subcommand:wordlist" help:"add hashes to a wordlist for use with, for example, shortscan"`
	Checksum *struct {
		Filename string `arg:"positional,required" help:"filename to checksum"`
		Original bool   `arg:"-o" help:"use the original (Windows Server 2003 + Windows XP) algorithm" default:"false"`
	} `arg:"subcommand:checksum" help:"generate a one-off checksum for the given filename"`
}

// Regular expression to strip URL parameters
var paramRegex = regexp.MustCompile("[?;#&\r\n]")

// Remove spaces and dots, translate the special 7 characters : + , ; = [ ] into underscores
// Special character rules taken from the leaked Windows 2003 source (gen8dot3.c)
var shortReplacer = strings.NewReplacer(" ", "", ".", "", ":", "_", "+", "_", ",", "_", ";", "_", "=", "_", "[", "_", "]", "_")

// stripNonASCII deletes every character outside the ASCII range. Per
// [MS-FSCC] 2.1.5.2.1, an 8.3 short name "MUST only contain characters that
// can be represented in ASCII" and "illegal characters ... are deleted from
// long filenames" — so an accented or non-Latin character isn't translated
// to an underscore like the shortReplacer set, it's dropped entirely. Runs
// after shortReplacer, whose replacements are all themselves ASCII.
func stripNonASCII(s string) string {
	var b strings.Builder
	b.Grow(len(s))
	for _, r := range s {
		if r < 0x80 {
			b.WriteRune(r)
		}
	}
	return b.String()
}

// Version
const version = "0.6"

// Checksum calculates the short filename checksum for the given filename
// Based on: https://tomgalvin.uk/assets/8dot3-checksum.c
// Docs: https://tomgalvin.uk/blog/gen/2015/06/09/filenames/
//
// The reference C loops over a PWSTR (UTF-16 code units), not Unicode code
// points. For any character outside the Basic Multilingual Plane, NTFS
// sees a surrogate pair — two 16-bit units — and the checksum loop runs
// twice for it. Encoding to UTF-16 first (rather than ranging over the
// string, which yields one full code point per iteration) is what makes
// that match for non-BMP filenames; BMP characters are unaffected since a
// UTF-16 code unit and a Go rune are the same value there.
func Checksum(f string) string {

	var ck uint16
	for _, c := range utf16.Encode([]rune(f)) {
		ck = ck*0x25 + c
	}

	t := int32(math.Abs(float64(int32(ck) * 314159269)))
	t -= int32(((uint64(t) * uint64(1152921497)) >> 60) * uint64(1000000007))

	ck = uint16(t)
	ck = (ck&0xf000)>>12 | (ck&0x0f00)>>4 | (ck&0x00f0)<<4 | (ck&0x000f)<<12

	return fmt.Sprintf("%04X", ck)

}

// ChecksumOriginal calculates the checksum for the given filename using the
// older of Microsoft's two checksum algorithms. This function is my translation
// of the checksum algorithm contained in the leaked Windows 2003 Server source
func ChecksumOriginal(f string) string {

	// Guard the paired seed: filenames shorter than two bytes would panic on
	// f[0]/f[1]. Names this short never need an 8.3 alias, so their checksum is
	// only ever reached through the one-off `checksum` command — handle it
	// without crashing rather than requiring the caller to pre-validate.
	var ck uint16
	switch {
	case len(f) >= 2:
		ck = (uint16(f[0])<<8 + uint16(f[1])) & 0xffff
		for i := 2; i < len(f); i += 2 {
			if ck&1 == 1 {
				ck = 0x8000 + ck>>1 + uint16(f[i])<<8
			} else {
				ck = ck>>1 + uint16(f[i])<<8
			}
			if i+1 < len(f) {
				ck += uint16(f[i+1]) & 0xffff
			}
		}
	case len(f) == 1:
		ck = uint16(f[0]) << 8
	}

	ck = (ck&0xf000)>>12 | (ck&0x0f00)>>4 | (ck&0x00f0)<<4 | (ck&0x000f)<<12
	return fmt.Sprintf("%04X", ck)

}

// Gen8dot3 returns the Windows short filename for a given filename (sans tilde)
func Gen8dot3(file string, ext string) (bool, string, string) {

	// Upper case the filename and and replace special characters
	fu := strings.ToUpper(file)
	fr := stripNonASCII(shortReplacer.Replace(fu))

	// Upper case the extension and replace special characters
	eu := strings.ToUpper(ext)
	er := stripNonASCII(shortReplacer.Replace(eu))

	// Determine whether a short filename was required
	r := len(file) > 8 || len(ext) > 3 || fu != fr || eu != er

	// Trim and return the names. fr/er are guaranteed pure ASCII (one byte
	// per character) by stripNonASCII, so slicing by byte count here is the
	// same as slicing by character count.
	return r, fr[:maths.Min(len(fr), 6)], er[:maths.Min(len(er), 3)]

}

// ChecksumWords turns a list of words into a word/checksum map. variants adds
// checksums for the case-folded forms of each word on top of the word's own.
func ChecksumWords(fh io.Reader, paramRegex *regexp.Regexp, variants bool) []wordlistRecord {

	// Loop through each word in the wordlist
	var wc []wordlistRecord
	s := bufio.NewScanner(fh)
	for s.Scan() {

		// Unescape any URL-encoded characters
		w, _ := url.PathUnescape(s.Text())
		w, _ = url.PathUnescape(w)

		// Remove any path elements, anything that looks like a parameter, trim whitespace and remove tabs
		// (note: filename case is retained as checksums will differ)
		w = path.Base(w)
		w = paramRegex.Split(w, 2)[0]
		w = strings.TrimSpace(w)
		w = strings.ReplaceAll(w, "\t", "")

		// Split the file and extension
		var f, e string
		if p := strings.LastIndex(w, "."); p > 0 && w[0] != '.' {
			f, e = w[:p], w[p+1:]
		} else {
			f, e = w, ""
		}

		// Generate an 8.3 filename for the word
		r, f83, e83 := Gen8dot3(f, e)

		// Skip the word if Windows wouldn't generate a short filename
		if !r {
			continue
		}

		// Always emit the word's own checksum so a rainbow can still resolve
		// checksummed collision-mode aliases (PPHHHH~N); --variants adds the
		// case-folded forms, because NTFS computes the checksum over the stored
		// case, which the attacker does not know in advance.
		vs := make(map[string]struct{})
		vs[Checksum(w)] = struct{}{}
		if variants {
			vs[Checksum(strings.ToLower(w))] = struct{}{}
			vs[Checksum(strings.ToUpper(w))] = struct{}{}
			vs[Checksum(strings.Title(w))] = struct{}{}
		}
		// Concatenate the variant checksums in sorted order so the rainbow
		// output is deterministic (map iteration order is randomised). shortscan
		// reads the field as an unordered set of 4-char chunks (mergeChecksums),
		// so ordering never affects matching — only reproducibility.
		keys := make([]string, 0, len(vs))
		for v := range vs {
			keys = append(keys, v)
		}
		sort.Strings(keys)
		c := strings.Join(keys, "")

		// Add the wordlist entry to the list
		wc = append(wc, wordlistRecord{c, f, e, f83, e83})

	}

	// Return the word/checksum map
	return wc

}

// Run is the main entry point for using utuilities from the command line
func Run() {

	// Parse command-line arguments
	p := arg.MustParse(&args)
	if p.Subcommand() == nil {
		fmt.Println(color.New(color.FgBlue, color.Bold).Sprint("Shortutil v"+version), "·", color.New(color.FgWhite, color.Bold).Sprint("a short filename utility by bitquark & TheZakMan"))
		p.WriteHelp(os.Stderr)
		os.Exit(1)
	}

	// Set the data source
	var fh io.Reader

	switch {

	// Process a wordlist
	case args.Wordlist != nil:

		// Open the wordlist
		f, err := os.Open(args.Wordlist.Filename)
		if err != nil {
			log.Fatalf("Error: %s\n", err)
		}
		defer f.Close()
		fh = f

		// Ouput the header and start checksumming
		fmt.Println("#SHORTSCAN#")
		words := make(map[string]struct{})
		for _, w := range ChecksumWords(fh, paramRegex, args.Wordlist.Variants) {

			// Upper case the wordlist entry
			var f, e string
			if args.Wordlist.KeepCase {
				f, e = w.filename, w.extension
			} else {
				f, e = strings.ToUpper(w.filename), strings.ToUpper(w.extension)
			}

			// Uniq the entry
			if args.Wordlist.Uniq {
				fe := f + "." + e
				if _, a := words[fe]; a {
					continue
				}
				words[fe] = struct{}{}
			}

			// Output the entry
			fmt.Printf("%s\t%s\t%s\t%s\t%s\n", w.checksum, w.filename83, w.extension83, f, e)

		}

	// Generate a one-off checksum
	case args.Checksum != nil:
		var c string
		if args.Checksum.Original {
			c = ChecksumOriginal(args.Checksum.Filename)
		} else {
			c = Checksum(args.Checksum.Filename)
		}
		fmt.Println(c)
	}

}
