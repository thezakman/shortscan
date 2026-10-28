package shortscan

import (
	"reflect"
	"testing"
)

func TestIndexChainURLs(t *testing.T) {
	defer func() { args.Index = false; args.Auto = false; args.Full = false }()

	// Disabled: no -i/--full -> nil, including plain --auto (which no longer sweeps).
	args.Index, args.Auto, args.Full = false, false, false
	if got := indexChainURLs("http://h/app/"); got != nil {
		t.Fatalf("disabled: expected nil, got %v", got)
	}
	args.Index, args.Auto, args.Full = false, true, false
	if got := indexChainURLs("http://h/app/"); got != nil {
		t.Fatalf("plain --auto no longer sweeps: expected nil, got %v", got)
	}

	// -i (the sweep modifier): the source/secret-bearing reserved + MVC folders.
	args.Index, args.Auto, args.Full = true, false, false
	got := indexChainURLs("http://h/app")
	want := []string{
		"http://h/app/bin::$INDEX_ALLOCATION/",
		"http://h/app/App_Code::$INDEX_ALLOCATION/",
		"http://h/app/App_Data::$INDEX_ALLOCATION/",
		"http://h/app/Views::$INDEX_ALLOCATION/",
		"http://h/app/Models::$INDEX_ALLOCATION/",
		"http://h/app/Controllers::$INDEX_ALLOCATION/",
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("index: got %v, want %v", got, want)
	}

	// Guard: never chain into an existing INDEX_ALLOCATION / ADS URL.
	if got := indexChainURLs("http://h/app/bin::$INDEX_ALLOCATION/"); got != nil {
		t.Fatalf("chain-of-chain: expected nil, got %v", got)
	}
	if got := indexChainURLs("http://h/app/web.config::$DATA"); got != nil {
		t.Fatalf("ADS url: expected nil, got %v", got)
	}

	// Pointed directly at a reserved folder (e.g. `shortscan https://h/bin -i --auto`):
	// probe it in place instead of nesting a second copy beneath it.
	args.Index, args.Auto, args.Full = true, true, false
	if got := indexChainURLs("http://h/bin/"); !reflect.DeepEqual(got, []string{"http://h/bin::$INDEX_ALLOCATION/"}) {
		t.Fatalf("self bin: got %v", got)
	}
	if got := indexChainURLs("http://h/bin"); !reflect.DeepEqual(got, []string{"http://h/bin::$INDEX_ALLOCATION/"}) {
		t.Fatalf("self bin (no trailing slash): got %v", got)
	}
	if got := indexChainURLs("http://h/App_Code/"); !reflect.DeepEqual(got, []string{"http://h/App_Code::$INDEX_ALLOCATION/"}) {
		t.Fatalf("self App_Code: got %v", got)
	}
	// Case-insensitive match, and a nested app root's own /bin still resolves in place.
	if got := indexChainURLs("http://h/app/BIN/"); !reflect.DeepEqual(got, []string{"http://h/app/BIN::$INDEX_ALLOCATION/"}) {
		t.Fatalf("self BIN case-insensitive: got %v", got)
	}

	// --full: the complete reserved-folder set.
	args.Index, args.Auto, args.Full = false, false, true
	got = indexChainURLs("http://h/app/")
	if len(got) != len(sourceLeakFoldersFull) {
		t.Fatalf("full: got %d urls %v, want %d", len(got), got, len(sourceLeakFoldersFull))
	}
	for i, f := range sourceLeakFoldersFull {
		want := "http://h/app/" + f + "::$INDEX_ALLOCATION/"
		if got[i] != want {
			t.Fatalf("full[%d] = %q, want %q", i, got[i], want)
		}
	}
}

// TestRedirectReservedFolderURL locks in the fix for a live "wtf?" moment: `shortscan
// https://h/bin -F --auto -i` printed TWO contradictory fingerprint+verdict blocks for
// the SAME host — a guaranteed-negative "8.3 oracle: no" / "Vulnerable: No" for the bare
// `/bin/` URL (a directory alone never has a differential oracle), immediately followed
// by the real "8.3 oracle: yes" for the separately-discovered `/bin::$INDEX_ALLOCATION/`.
// redirectReservedFolderURL now rewrites the user's own top-level target up front so
// there is only ever ONE scan of a reserved folder, not a doomed one plus a real one.
func TestRedirectReservedFolderURL(t *testing.T) {
	defer func() { args.Index = false; args.Auto = false; args.Full = false }()

	// Disabled without -i/--full: even --auto alone leaves a reserved-folder target
	// untouched (matches indexChainURLs' "plain --auto no longer sweeps").
	args.Index, args.Auto, args.Full = false, true, false
	if got := redirectReservedFolderURL("http://h/bin"); got != "http://h/bin" {
		t.Fatalf("disabled: got %q, want unchanged", got)
	}

	// -i + --auto: the exact live repro. `/bin` (no trailing slash) and `/bin/` both
	// redirect to the ADS form instead of being scanned as a bare, oracle-less directory.
	args.Index, args.Auto, args.Full = true, true, false
	if got := redirectReservedFolderURL("https://h/bin"); got != "https://h/bin::$INDEX_ALLOCATION/" {
		t.Fatalf("bin no-slash: got %q", got)
	}
	if got := redirectReservedFolderURL("https://h/bin/"); got != "https://h/bin::$INDEX_ALLOCATION/" {
		t.Fatalf("bin trailing-slash: got %q", got)
	}
	// Case-insensitive, and nested under an app root.
	if got := redirectReservedFolderURL("https://h/app/BIN"); got != "https://h/app/BIN::$INDEX_ALLOCATION/" {
		t.Fatalf("nested case-insensitive: got %q", got)
	}

	// A non-reserved target (the ordinary case) is left completely alone.
	if got := redirectReservedFolderURL("https://h/uploads/"); got != "https://h/uploads/" {
		t.Fatalf("non-reserved: got %q, want unchanged", got)
	}

	// Idempotent: a URL already carrying the ADS token is never double-wrapped.
	if got := redirectReservedFolderURL("https://h/bin::$INDEX_ALLOCATION/"); got != "https://h/bin::$INDEX_ALLOCATION/" {
		t.Fatalf("already-ADS: got %q, want unchanged", got)
	}

	// --full recognises the wider reserved set too (e.g. Areas, only in the full list).
	args.Index, args.Auto, args.Full = false, false, true
	if got := redirectReservedFolderURL("https://h/Areas"); got != "https://h/Areas::$INDEX_ALLOCATION/" {
		t.Fatalf("full-only folder: got %q", got)
	}
}
