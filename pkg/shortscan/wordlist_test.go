package shortscan

import (
	"io"
	"strings"
	"testing"
)

// A "." or ".." wordlist line must never become record.filename — every recovery
// path that resolves a candidate turns filename+extension into a URL path
// segment (recovery.go), and --recurse's foundDirectories accepts it verbatim.
// Same guard class as references.go and aliasprobe.go apply to untrusted path
// segments; here it's defense-in-depth against a malformed/hostile -w file.
func TestWordlistRejectsDotSegmentLines(t *testing.T) {
	wc := newWordlistConfig([]wordlistSource{{
		name: "dotsegments",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader(".\n..\nLogin.aspx\n")), nil
		},
	}})
	wc.startLoading()
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	if len(wc.wordlist) != 1 {
		t.Fatalf("loaded %d records, want 1 (dot-segment lines must be dropped): %#v", len(wc.wordlist), wc.wordlist)
	}
	if wc.wordlist[0].filename != "Login" || wc.wordlist[0].extension != ".aspx" {
		t.Fatalf("unexpected surviving record: %#v", wc.wordlist[0])
	}
}
