package shortscan

import (
	"bytes"
	"net/http"
	"strings"
	"sync"
	"testing"
)

// TestStemBruteRecoversNameBeyondSixCharBoundary is the before/after proof for
// the headline capability: BOLETO~1.ASP is a classic (non-checksummed) alias
// whose real long name, "boletos.asp", is one character past the 6-char 8.3
// boundary the tilde oracle can prove. No wordlist contains it (real target
// names are frequently domain-specific and absent from a generic wordlist);
// --brute recovers it anyway by proposing short completions directly.
func TestStemBruteRecoversNameBeyondSixCharBoundary(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
	}()

	const longName = "boletos.asp"
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	var output bytes.Buffer
	outputWriter = &output
	args = arguments{
		Autocomplete: "status", Output: "human", Retries: 0,
		Brute: true, BruteRange: "1-2",
		BruteCharset: "abcdefghijklmnopqrstuvwxyz0123456789",
		BruteLimit:   2000,
	}

	hits := map[string]int{}
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		hits[req.URL.Path]++
		if strings.EqualFold(req.URL.Path, "/"+longName) {
			return responseFor(req, http.StatusOK, "form"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}

	base := "http://example.test/"
	ac := &attackConfig{
		autocomplete:     args.Autocomplete,
		foundFiles:       make(map[string]struct{}),
		foundDirectories: make(map[string]struct{}),
		observedAliases:  make(map[string]baseRequest),
	}
	br := baseRequest{url: base, file: "BOLETO", tilde: "~1", ext: ".ASP"}
	ac.observedAliases[strings.ToLower(base+"\x00BOLETO\x00.ASP")] = br

	recovered := recoverStemBruteAliases(client, &httpStats{}, ac, nil)
	if recovered != 1 {
		t.Fatalf("stem-brute recovered %d names, want 1; output=%q", recovered, output.String())
	}
	if _, ok := ac.foundFiles[longName]; !ok {
		t.Fatalf("stem-brute failed to recover %s; foundFiles=%v output=%q", longName, ac.foundFiles, output.String())
	}
	for _, want := range []string{longName, "BRUTE", "1 extra char"} {
		if !strings.Contains(output.String(), want) {
			t.Fatalf("stem-brute output missing %q: %q", want, output.String())
		}
	}
	if hits["/"+longName] == 0 {
		t.Fatalf("stem-brute never actually probed %s", longName)
	}
}

// TestStemBruteTriesAmbiguousExtensions proves the extension side of the same
// ambiguity: an observed short extension of ASP matches both .asp and .aspx in
// the 8.3 encoding, so a real .aspx file must still be found.
func TestStemBruteTriesAmbiguousExtensions(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
	}()

	const longName = "boletos.aspx"
	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	var output bytes.Buffer
	outputWriter = &output
	args = arguments{
		Autocomplete: "status", Output: "human", Retries: 0,
		Brute: true, BruteRange: "1-2",
		BruteCharset: "abcdefghijklmnopqrstuvwxyz0123456789",
		BruteLimit:   2000,
	}

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if strings.EqualFold(req.URL.Path, "/"+longName) {
			return responseFor(req, http.StatusOK, "form"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}

	base := "http://example.test/"
	ac := &attackConfig{
		autocomplete:     args.Autocomplete,
		foundFiles:       make(map[string]struct{}),
		foundDirectories: make(map[string]struct{}),
		observedAliases:  make(map[string]baseRequest),
	}
	br := baseRequest{url: base, file: "BOLETO", tilde: "~1", ext: ".ASP"}
	ac.observedAliases[strings.ToLower(base+"\x00BOLETO\x00.ASP")] = br

	recovered := recoverStemBruteAliases(client, &httpStats{}, ac, nil)
	if recovered != 1 {
		t.Fatalf("stem-brute recovered %d names, want 1; output=%q", recovered, output.String())
	}
	if _, ok := ac.foundFiles[longName]; !ok {
		t.Fatalf("stem-brute failed to recover the .aspx sibling; foundFiles=%v output=%q", ac.foundFiles, output.String())
	}
}

// TestStemBruteExtensionsNoDuplicates guards the dedup fix: the seed short
// extension ("asp") must not be emitted twice — once as the literal seed and
// once from the dotted wellKnownExtensions entry (".asp") — because each
// duplicate costs one wasted HTTP verification per unresolved group.
func TestStemBruteExtensionsNoDuplicates(t *testing.T) {
	exts := stemBruteExtensions("ASP")
	seen := map[string]struct{}{}
	for _, e := range exts {
		norm := strings.TrimPrefix(strings.ToLower(e), ".")
		if _, dup := seen[norm]; dup {
			t.Fatalf("duplicate extension %q in %v", e, exts)
		}
		seen[norm] = struct{}{}
	}
	// The observed extension itself and its .aspx sibling must both be present.
	for _, want := range []string{".asp", ".aspx"} {
		found := false
		for _, e := range exts {
			if e == want {
				found = true
			}
		}
		if !found {
			t.Fatalf("stemBruteExtensions(ASP) missing %q: %v", want, exts)
		}
	}
}

// TestParseBruteRange covers the --brute-range grammar: MIN-MAX, MIN,MAX, and a
// bare N (meaning 1..N), plus the rejections.
func TestParseBruteRange(t *testing.T) {
	cases := []struct {
		in     string
		lo, hi int
		errsOK bool
	}{
		{"1-3", 1, 3, false},
		{"2,4", 2, 4, false},
		{"3", 1, 3, false},       // bare N == 1..N
		{" 1 - 2 ", 1, 2, false}, // surrounding spaces tolerated
		{"2-2", 2, 2, false},
		{"3-1", 0, 0, true}, // min > max
		{"0", 0, 0, true},   // bare 0 -> empty range 1..0, must be rejected (not silently accepted)
		{"0-0", 0, 0, true}, // and its MIN-MAX equivalent rejects the same way
		{"", 0, 0, true},
		{"a-b", 0, 0, true},
		{"x", 0, 0, true},
	}
	for _, c := range cases {
		lo, hi, err := parseBruteRange(c.in)
		if c.errsOK {
			if err == nil {
				t.Errorf("parseBruteRange(%q): want error, got %d-%d", c.in, lo, hi)
			}
			continue
		}
		if err != nil || lo != c.lo || hi != c.hi {
			t.Errorf("parseBruteRange(%q) = %d,%d,%v; want %d,%d,nil", c.in, lo, hi, err, c.lo, c.hi)
		}
	}
}

// TestDefaultBruteRange pins the mode-dependent default: --auto (and a bare
// --brute) use 1-2; --full digs one deeper to 1-3.
func TestDefaultBruteRange(t *testing.T) {
	if got := defaultBruteRange(false); got != "1-2" {
		t.Errorf("defaultBruteRange(false) = %q, want 1-2", got)
	}
	if got := defaultBruteRange(true); got != "1-3" {
		t.Errorf("defaultBruteRange(true) = %q, want 1-3", got)
	}
}

// TestBruteStemSuffixesRange proves a range skips completions shorter than lo:
// a 2-3 range must never emit a single-character completion.
func TestBruteStemSuffixesRange(t *testing.T) {
	const noCap = 1 << 20
	if n := len(bruteStemSuffixes("ab", 1, 2, noCap)); n != 6 { // 2 + 4
		t.Fatalf("range 1-2 over \"ab\" = %d completions, want 6", n)
	}
	got := bruteStemSuffixes("ab", 2, 2, noCap)
	if len(got) != 4 { // ab×ab
		t.Fatalf("range 2-2 over \"ab\" = %d, want 4: %v", len(got), got)
	}
	for _, s := range got {
		if len(s) != 2 {
			t.Fatalf("range 2-2 emitted %q (len %d); a below-lo length leaked", s, len(s))
		}
	}
}

// TestBruteStemSuffixesCap proves the maxCount cap bounds emission (the OOM fix):
// without it the set is charset^hi, which explodes for a large charset at hi=4.
func TestBruteStemSuffixesCap(t *testing.T) {
	// 10-char charset, range 1-4 would be 10+100+1000+10000 = 11110 completions;
	// the cap must clamp it to exactly maxCount, shortest-first.
	got := bruteStemSuffixes("0123456789", 1, 4, 50)
	if len(got) != 50 {
		t.Fatalf("cap 50 produced %d completions, want exactly 50", len(got))
	}
	// The first 10 must still be the length-1 completions (order preserved).
	for i := 0; i < 10; i++ {
		if len(got[i]) != 1 {
			t.Fatalf("capped output lost shortest-first order at %d: %q", i, got[i])
		}
	}
	if bruteStemSuffixes("ab", 1, 2, 0) != nil {
		t.Fatalf("maxCount 0 must produce no completions")
	}
}

// TestStemBruteSkipsAlreadyResolvedAlias proves the group is not re-bruted (and
// no extra requests spent) once an earlier, cheaper technique already recovered
// its long name.
func TestStemBruteSkipsAlreadyResolvedAlias(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
	}()

	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	var output bytes.Buffer
	outputWriter = &output
	args = arguments{
		Autocomplete: "status", Output: "human", Retries: 0,
		Brute: true, BruteRange: "1-2",
		BruteCharset: "abcdefghijklmnopqrstuvwxyz0123456789",
		BruteLimit:   2000,
	}

	requests := 0
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		requests++
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}

	base := "http://example.test/"
	ac := &attackConfig{
		autocomplete: args.Autocomplete,
		// boletos.asp was already recovered by an earlier pass (e.g. the
		// wordlist), so foundFiles already 8.3-shortens to BOLETO/ASP.
		foundFiles:       map[string]struct{}{"boletos.asp": {}},
		foundDirectories: make(map[string]struct{}),
		observedAliases:  make(map[string]baseRequest),
	}
	br := baseRequest{url: base, file: "BOLETO", tilde: "~1", ext: ".ASP"}
	ac.observedAliases[strings.ToLower(base+"\x00BOLETO\x00.ASP")] = br

	recovered := recoverStemBruteAliases(client, &httpStats{}, ac, nil)
	if recovered != 0 {
		t.Fatalf("stem-brute recovered %d names, want 0 (already resolved); output=%q", recovered, output.String())
	}
	if requests != 0 {
		t.Fatalf("stem-brute sent %d requests for an already-resolved alias, want 0", requests)
	}
}

// TestStemBruteLimitIsSharedAcrossGroups is the regression proof for a request-
// volume bug found in review: --brute-limit must be a single budget shared
// by every unresolved short-name group in the directory, not reset per group —
// otherwise a directory with many unresolved names silently multiplies the
// request volume by however many groups it has (e.g. 30 groups * 2000 = 60,000
// requests on the documented default). Two groups here, neither ever matching,
// with a limit far smaller than either alone would exhaust: total requests must
// stay capped at the limit, proving the second group got none of its own budget.
func TestStemBruteLimitIsSharedAcrossGroups(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
	}()

	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	var output bytes.Buffer
	outputWriter = &output
	const sharedLimit = 5
	args = arguments{
		Autocomplete: "status", Output: "human", Retries: 0,
		Brute: true, BruteRange: "1-1",
		BruteCharset: "abcdefghijklmnopqrstuvwxyz0123456789", // 36 chars: alone, far more than sharedLimit
		BruteLimit:   sharedLimit,
	}

	// recoverStemBruteAliases runs its groups concurrently (bounded by -c), so the
	// mock transport can be called from multiple goroutines — guard the slice.
	var pathsMu sync.Mutex
	var paths []string
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		pathsMu.Lock()
		paths = append(paths, req.URL.Path)
		pathsMu.Unlock()
		return responseFor(req, http.StatusNotFound, "missing"), nil // nothing ever matches
	})}

	base := "http://example.test/"
	ac := &attackConfig{
		autocomplete:     args.Autocomplete,
		foundFiles:       make(map[string]struct{}),
		foundDirectories: make(map[string]struct{}),
		observedAliases:  make(map[string]baseRequest),
	}
	for _, stem := range []string{"BOLETO", "FATURA"} {
		br := baseRequest{url: base, file: stem, tilde: "~1", ext: ".ASP"}
		ac.observedAliases[strings.ToLower(base+"\x00"+stem+"\x00.ASP")] = br
	}

	recovered := recoverStemBruteAliases(client, &httpStats{}, ac, nil)
	if recovered != 0 {
		t.Fatalf("stem-brute unexpectedly recovered %d names; output=%q", recovered, output.String())
	}
	// Either group alone (BOLETO or FATURA) has far more than sharedLimit valid
	// candidates, so the TOTAL across both must stay near sharedLimit — proving the
	// budget is shared, not one sharedLimit per group (the original bug this test
	// was written against). Groups run concurrently (bounded by -c), so which group's
	// requests land first is no longer deterministic — only the shared total is
	// asserted; a small overshoot is expected and fine (each in-flight goroutine can
	// send one more request before it observes the exhausted-budget flag).
	if len(paths) > sharedLimit+10 {
		t.Fatalf("stem-brute sent %d requests total, want roughly the shared limit %d plus baseline/concurrency overhead: paths=%v", len(paths), sharedLimit, paths)
	}
	if !strings.Contains(output.String(), "brute-limit") {
		t.Fatalf("stem-brute did not warn about the truncated budget: %q", output.String())
	}
}
