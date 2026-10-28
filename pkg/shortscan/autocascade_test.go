package shortscan

import (
	"net/http"
	"reflect"
	"strings"
	"sync"
	"testing"
)

// --auto / --full must turn on the retrieval chain, and opportunistically read the
// Mark-of-the-Web ADS when the operator named no explicit stream.
func TestApplyAutoCascadeEnablesRetrievalChain(t *testing.T) {
	for _, mode := range []string{"auto", "full"} {
		a := arguments{}
		switch mode {
		case "auto":
			a.Auto = true
		case "full":
			a.Full = true
		}
		applyAutoCascade(&a)

		if !a.Retrieve {
			t.Fatalf("%s: expected Retrieve to be enabled", mode)
		}
		if !a.WebDAV || !a.TildeContinuation || !a.Brute || !a.Fingerprint {
			t.Fatalf("%s: expected the recovery cascade to be enabled", mode)
		}
		if !reflect.DeepEqual(a.RetrieveStreams, []string{motwStream}) {
			t.Fatalf("%s: expected RetrieveStreams=[%s], got %v", mode, motwStream, a.RetrieveStreams)
		}
	}
}

// --full is strictly a superset: it also arms the active probes.
func TestApplyAutoCascadeFullArmsActiveProbes(t *testing.T) {
	auto := arguments{Auto: true}
	applyAutoCascade(&auto)
	if auto.ProbeCandidates || auto.InspectSource {
		t.Fatalf("--auto must not arm active probes (ProbeCandidates=%v InspectSource=%v)", auto.ProbeCandidates, auto.InspectSource)
	}
	full := arguments{Full: true}
	applyAutoCascade(&full)
	if !full.ProbeCandidates || !full.InspectSource {
		t.Fatalf("--full must arm active probes (ProbeCandidates=%v InspectSource=%v)", full.ProbeCandidates, full.InspectSource)
	}
}

// An operator-supplied --retrieve-stream must never be overridden by the opportunistic
// Mark-of-the-Web default.
func TestApplyAutoCascadeKeepsOperatorStreams(t *testing.T) {
	a := arguments{Auto: true, RetrieveStreams: []string{"SmartScreen"}}
	applyAutoCascade(&a)
	if !reflect.DeepEqual(a.RetrieveStreams, []string{"SmartScreen"}) {
		t.Fatalf("operator streams overridden: got %v", a.RetrieveStreams)
	}
}

// Without --auto/--full the cascade is a no-op: nothing is enabled and no stream is added.
func TestApplyAutoCascadeNoopWhenDisabled(t *testing.T) {
	a := arguments{}
	applyAutoCascade(&a)
	if a.Retrieve || a.WebDAV || len(a.RetrieveStreams) != 0 {
		t.Fatalf("cascade ran without --auto/--full: %+v", a)
	}
}

// Integration guard: the expanded --auto arguments must drive both the canonical
// cross-stack read and the bounded Mark-of-the-Web read. Each successful variant
// must also send its own same-shape negative control.
func TestAutoCascadeRetrievesCanonicalAndMOTW(t *testing.T) {
	previousArgs := args
	defer func() { args = previousArgs }()

	var mu sync.Mutex
	var paths []string
	client := &http.Client{Transport: roundTripFunc(func(r *http.Request) (*http.Response, error) {
		mu.Lock()
		paths = append(paths, r.URL.Path)
		mu.Unlock()
		switch r.URL.Path {
		case "/dir/CONFID~1.TXT":
			return responseFor(r, http.StatusOK, "main-canary"), nil
		case "/dir/CONFID~1.TXT:Zone.Identifier:$DATA":
			return responseFor(r, http.StatusOK, "[ZoneTransfer]\\nZoneId=3"), nil
		default:
			return responseFor(r, http.StatusNotFound, "not found"), nil
		}
	})}

	args = arguments{
		Auto:         true,
		RetrieveBase: "http://retrieve.test",
		LootDir:      t.TempDir(),
		Output:       "ndjson",
	}
	applyAutoCascade(&args)
	retrieveShortName(client, &httpStats{}, &attackConfig{}, baseRequest{
		url: "http://iis.example/dir/", file: "CONFID", tilde: "~1", ext: ".TXT",
	})

	mu.Lock()
	joined := strings.Join(paths, "\n")
	mu.Unlock()
	for _, want := range []string{
		"/dir/CONFID~1.TXT",
		"/dir/CONFID~1.TXT:Zone.Identifier:$DATA",
	} {
		if !strings.Contains(joined, want) {
			t.Fatalf("automatic retrieval did not request %s; paths:\n%s", want, joined)
		}
	}
	canonicalControls, streamControls := 0, 0
	for _, p := range paths {
		switch {
		case p == "/dir/CONFID~1.TXT", p == "/dir/CONFID~1.TXT:Zone.Identifier:$DATA":
		case strings.HasSuffix(p, "~1.TXT:Zone.Identifier:$DATA"):
			streamControls++
		case strings.HasSuffix(p, "~1.TXT"):
			canonicalControls++
		}
	}
	if canonicalControls != 1 || streamControls != 1 {
		t.Fatalf("automatic reads need one control each; canonical=%d stream=%d paths:\n%s", canonicalControls, streamControls, joined)
	}
}
