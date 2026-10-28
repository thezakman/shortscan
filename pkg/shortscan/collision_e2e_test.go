package shortscan

import (
	"bytes"
	"io"
	"net/http"
	"regexp"
	"strings"
	"testing"

	"github.com/thezakman/shortscan/pkg/shortutil"
)

// TestChecksumMaskRecoversNameAbsentFromWordlist is the before/after proof for
// the headline capability: a hashed alias (App_Web_ab12.dll's 8.3 form) whose
// long name is in NO wordlist. Classic recovery can only report the collision
// group; --checksum-mask reconstructs and HTTP-verifies the full name.
func TestChecksumMaskRecoversNameAbsentFromWordlist(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousRegex, previousBruteStatuses := checksumRegex, bruteStatuses
	previousCandidateWriter := candidateOutputWriter
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		checksumRegex, bruteStatuses = previousRegex, previousBruteStatuses
		candidateOutputWriter = previousCandidateWriter
	}()

	const longName = "App_Web_ab12.dll"
	checksum := shortutil.Checksum(longName) // real Windows 8.3 collision checksum
	aliasFile := "AP" + checksum             // e.g. AP0DB6 (PP + HHHH)

	// The target exposes the long file at 200 and everything else at 404, exactly
	// what the status oracle needs. The hashed alias path itself stays blocked.
	newClient := func(hits *map[string]int) *http.Client {
		counts := map[string]int{}
		*hits = counts
		return &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
			counts[req.URL.Path]++
			switch req.URL.Path {
			case "/" + longName:
				return responseFor(req, http.StatusOK, "MZ...binary"), nil
			default:
				return responseFor(req, http.StatusNotFound, "missing"), nil
			}
		})}
	}

	baseAlias := func() baseRequest {
		return baseRequest{url: "http://example.test/", file: aliasFile, tilde: "~1", ext: ".DLL"}
	}
	freshConfig := func() *attackConfig {
		return &attackConfig{
			autocomplete:     args.Autocomplete,
			foundFiles:       make(map[string]struct{}),
			foundDirectories: make(map[string]struct{}),
		}
	}
	resetCaches := func() {
		statusCache = make(map[string]map[int]struct{})
		distanceCache = make(map[string]map[int]distances)
		checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
		bruteStatuses = map[int]struct{}{http.StatusOK: {}}
	}

	// --- BEFORE: no mask, a wordlist that does NOT contain the name ---
	var before bytes.Buffer
	outputWriter = &before
	args = arguments{
		Autocomplete: "none", Output: "human", ProbeCandidates: true, ProbeStatus: "200",
		Retries: 0,
	}
	resetCaches()
	wcEmpty := newWordlistConfig([]wordlistSource{{
		name: "unrelated",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader("Default.aspx\nLogin.aspx\n")), nil
		},
	}})
	if err := wcEmpty.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}
	var beforeHits map[string]int
	client := newClient(&beforeHits)
	acBefore := freshConfig()
	acBefore.wordlist = wcEmpty
	recoverLongName(client, &httpStats{}, acBefore, baseAlias())
	if _, ok := acBefore.foundFiles["app_web_ab12.dll"]; ok {
		t.Fatalf("baseline unexpectedly recovered the long name")
	}
	if strings.Contains(strings.ToLower(before.String()), "app_web_ab12") {
		t.Fatalf("baseline output leaked the long name it should not know: %q", before.String())
	}
	if beforeHits["/"+longName] != 0 {
		t.Fatalf("baseline should never have probed the long name (%d probes)", beforeHits["/"+longName])
	}

	// --- AFTER: --checksum-mask reconstructs the name from the checksum alone ---
	var after bytes.Buffer
	outputWriter = &after
	args = arguments{
		Autocomplete: "none", Output: "human", ProbeCandidates: true, ProbeStatus: "200",
		Retries:          0,
		ChecksumMasks:    []string{"App_Web_????.dll"},
		ChecksumAlphabet: "abcdefghijklmnopqrstuvwxyz0123456789",
		ChecksumLimit:    256,
	}
	resetCaches()
	var afterHits map[string]int
	client = newClient(&afterHits)
	acAfter := freshConfig()
	acAfter.wordlist = wcEmpty
	recoverLongName(client, &httpStats{}, acAfter, baseAlias())
	if _, ok := acAfter.foundFiles["app_web_ab12.dll"]; !ok {
		t.Fatalf("checksum-mask failed to recover the long name; output=%q", after.String())
	}
	out := after.String()
	for _, want := range []string{"App_Web_ab12.dll", "checksum-mask", "ck=" + checksum} {
		if !strings.Contains(out, want) {
			t.Fatalf("recovery output missing %q: %q", want, out)
		}
	}
}

// TestCollisionAncestryRecoversFromSaturatedFamily proves the second capability:
// a reference/wordlist name is joined to a checksummed sibling only because a
// saturated PRIMAX~1..~4 family is present and the 16-bit checksum matches.
func TestCollisionAncestryRecoversFromSaturatedFamily(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousStatusCache, previousDistanceCache := statusCache, distanceCache
	previousRegex := checksumRegex
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		statusCache, distanceCache = previousStatusCache, previousDistanceCache
		checksumRegex = previousRegex
	}()

	const longName = "PRIMAX5145"
	checksum := shortutil.Checksum(longName)
	aliasFile := "PR" + checksum

	statusCache = make(map[string]map[int]struct{})
	distanceCache = make(map[string]map[int]distances)
	checksumRegex = regexp.MustCompile("^.{1,2}[0-9A-F]{4}$")
	var output bytes.Buffer
	outputWriter = &output
	args = arguments{
		Autocomplete: "status", Output: "human", CollisionAncestry: true,
		Retries: 0,
	}

	wc := newWordlistConfig([]wordlistSource{{
		name: "words",
		open: func() (io.ReadCloser, error) {
			return io.NopCloser(strings.NewReader(longName + "\nPRIMAX0000\n")), nil
		},
	}})
	if err := wc.waitLoaded(); err != nil {
		t.Fatalf("waitLoaded: %v", err)
	}

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.URL.Path == "/"+longName {
			return responseFor(req, http.StatusOK, "hit"), nil
		}
		return responseFor(req, http.StatusNotFound, "missing"), nil
	})}

	base := "http://example.test/"
	ac := &attackConfig{
		autocomplete:     args.Autocomplete,
		wordlist:         wc,
		foundFiles:       make(map[string]struct{}),
		foundDirectories: make(map[string]struct{}),
		observedAliases:  make(map[string]baseRequest),
	}
	// The saturated classic family plus the hashed sibling, exactly as live
	// enumeration would have observed them.
	for _, tilde := range []string{"~1", "~2", "~3", "~4"} {
		br := baseRequest{url: base, file: "PRIMAX", tilde: tilde, ext: ""}
		ac.observedAliases[strings.ToLower(base+"\x00PRIMAX\x00"+tilde)] = br
	}
	ac.observedAliases[strings.ToLower(base+"\x00"+aliasFile+"\x00")] =
		baseRequest{url: base, file: aliasFile, tilde: "~1", ext: ""}

	recovered := recoverCollisionAncestryAliases(client, &httpStats{}, ac, nil)
	if recovered != 1 {
		t.Fatalf("collision-ancestry recovered %d names, want 1; output=%q", recovered, output.String())
	}
	if _, ok := ac.foundFiles[strings.ToLower(longName)]; !ok {
		t.Fatalf("ancestry failed to recover %s; output=%q", longName, output.String())
	}
	for _, want := range []string{longName, "COLLISION-ANCESTRY", "PRIMAX~*", "ck=" + checksum} {
		if !strings.Contains(output.String(), want) {
			t.Fatalf("ancestry output missing %q: %q", want, output.String())
		}
	}
}
