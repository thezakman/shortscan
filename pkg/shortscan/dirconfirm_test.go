package shortscan

import (
	"net/http"
	"regexp"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
)

func TestDirAliasNativeDistinguishesManagedVsNative(t *testing.T) {
	// /CONFID~1 -> managed ASP.NET 404 (no IIS detailed-error string);
	// everything else -> native IIS 404.0 detailed error (substatus + physical path).
	managed := `<html><head><title>Resource cannot be found</title></head><body>404</body></html>`
	native := `<html><head><title>IIS 10.0 - 404.0 - Not Found</title></head>` +
		`<body>Physical Path C:\inetpub\wwwroot\X~1</body></html>`
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.URL.Path == "/CONFID~1" {
			return responseFor(req, http.StatusNotFound, managed), nil
		}
		return responseFor(req, http.StatusNotFound, native), nil
	})}

	code, isNative, ok := dirAliasNative(client, &httpStats{}, "http://iis.test/", "CONFID~1")
	if !ok || code != 404 || isNative {
		t.Fatalf("real dir alias should be managed (native=false), got code=%d native=%v ok=%v", code, isNative, ok)
	}
	code, isNative, ok = dirAliasNative(client, &httpStats{}, "http://iis.test/", "ZZZZZZ~9")
	if !ok || code != 404 || !isNative {
		t.Fatalf("fake alias should be native (native=true), got code=%d native=%v ok=%v", code, isNative, ok)
	}
}

func TestSafeFakeShortIs83Shaped(t *testing.T) {
	re := regexp.MustCompile(`^[A-Z0-9]{1,6}~[0-9]$`)
	for i := 0; i < 50; i++ {
		f := safeFakeShort()
		if !re.MatchString(f) {
			t.Fatalf("safeFakeShort produced a non-8.3 name: %q", f)
		}
		if !strings.HasSuffix(f, "~9") {
			t.Fatalf("safeFakeShort should use the improbable ~9 ordinal: %q", f)
		}
	}
}

// TestAutoDirConfirmDirectoryAnnotatesRealDirsOnly locks in the auto-applied
// dirconfirm check added after comparing shortscan against the reference Java
// scanner (irsdl/IIS-ShortName-Scanner), which classifies folder-vs-file for an
// UNRESOLVED short name during normal enumeration — shortscan had the same
// underlying managed-vs-native technique (--dir-confirm) but never ran it
// automatically, so a directory recovered ONLY by its 8.3 alias (no wordlist/
// reference match) got no signal beyond the bare "?" placeholder. Verified live
// against a real IIS10 lab: an unresolved directory alias now prints "[DIR]",
// an unresolved FILE alias of the same collision-group prefix does not.
func TestAutoDirConfirmDirectoryAnnotatesRealDirsOnly(t *testing.T) {
	managed := `<html><head><title>Resource cannot be found</title></head><body>404</body></html>`
	native := `<html><head><title>IIS 10.0 - 404.0 - Not Found</title></head>` +
		`<body>Physical Path C:\inetpub\wwwroot\X~1</body></html>`
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		switch req.URL.Path {
		case "/REALDI~1": // a genuine directory: managed pipeline
			return responseFor(req, http.StatusNotFound, managed), nil
		case "/REALFI~1": // a genuine FILE (no extension known yet): native 404.0, same as absent
			return responseFor(req, http.StatusNotFound, native), nil
		default: // calibration probe (safeFakeShort) and anything else: native (absent)
			return responseFor(req, http.StatusNotFound, native), nil
		}
	})}
	defer func() { dirConfirmOracle = map[string]bool{} }() // isolate from other tests' cache

	if !autoDirConfirmDirectory(client, &httpStats{}, "http://iis.test/", "REALDI~1") {
		t.Error("a genuine directory alias must be confirmed [DIR]")
	}
	if autoDirConfirmDirectory(client, &httpStats{}, "http://iis.test/", "REALFI~1") {
		t.Error("a non-directory alias must NOT be confirmed as a directory")
	}
	// Calibration is cached per origin: only one calibration probe should ever
	// fire even across multiple candidate checks on the same host.
	calls := 0
	client2 := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		calls++
		return responseFor(req, http.StatusNotFound, native), nil
	})}
	dirConfirmOracle = map[string]bool{}
	autoDirConfirmDirectory(client2, &httpStats{}, "http://cached.test/", "A~1")
	autoDirConfirmDirectory(client2, &httpStats{}, "http://cached.test/", "B~1")
	autoDirConfirmDirectory(client2, &httpStats{}, "http://cached.test/", "C~1")
	if calls != 4 { // 1 calibration + 3 candidate checks, NOT 3 calibrations + 3 checks
		t.Errorf("expected calibration to run once and be cached, got %d total requests", calls)
	}
}

// TestAutoDirConfirmDirectoryUnusableOracleStaysSilent locks in that a target
// without the native detailed-404 signal (custom errors on, or non-IIS) never
// produces a false [DIR] annotation — the calibration probe itself must come
// back native-404 or the whole check silently no-ops.
func TestAutoDirConfirmDirectoryUnusableOracleStaysSilent(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		// Every path, including the calibration fake, gets the SAME generic
		// managed-looking 404 - the oracle can't distinguish anything.
		return responseFor(req, http.StatusNotFound, "generic 404 page"), nil
	})}
	defer func() { dirConfirmOracle = map[string]bool{} }()
	if autoDirConfirmDirectory(client, &httpStats{}, "http://flat.test/", "ANYNAM~1") {
		t.Error("an unusable oracle (calibration didn't come back native) must never confirm a directory")
	}
}

// TestAutoDirConfirmDirectoryConcurrentSameOrigin stress-tests the per-origin
// calibration cache under real concurrency (enumerate() runs char-discovery
// workers concurrently, so multiple candidates on the SAME origin genuinely can
// race to calibrate at once) — run with -race to catch a lock ordering bug.
func TestAutoDirConfirmDirectoryConcurrentSameOrigin(t *testing.T) {
	native := `<html><head><title>IIS 10.0 - 404.0 - Not Found</title></head>` +
		`<body>Physical Path C:\inetpub\wwwroot\X~1</body></html>`
	managed := `<html><head><title>Resource cannot be found</title></head><body>404</body></html>`
	var calib int32 // count calibration probes (the fake ~9 name)
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if strings.Contains(req.URL.Path, "~9") { // safeFakeShort() uses the ~9 ordinal
			atomic.AddInt32(&calib, 1)
			return responseFor(req, http.StatusNotFound, native), nil // usable oracle
		}
		if strings.HasPrefix(req.URL.Path, "/DIR") {
			return responseFor(req, http.StatusNotFound, managed), nil
		}
		return responseFor(req, http.StatusNotFound, native), nil
	})}
	defer func() {
		dirConfirmOracle = map[string]bool{}
		dirConfirmOnce = map[string]*sync.Once{}
	}()
	dirConfirmOracle = map[string]bool{}
	dirConfirmOnce = map[string]*sync.Once{}

	var wg sync.WaitGroup
	for i := 0; i < 20; i++ {
		wg.Add(1)
		go func(n int) {
			defer wg.Done()
			name := "DIR" + string(rune('A'+n)) + "~1"
			if !autoDirConfirmDirectory(client, &httpStats{}, "http://concurrent.test/", name) {
				t.Errorf("goroutine %d: expected directory confirmed", n)
			}
		}(i)
	}
	wg.Wait()
	// Single-flight: exactly one calibration probe for the origin, not one per worker.
	if got := atomic.LoadInt32(&calib); got != 1 {
		t.Fatalf("expected exactly 1 calibration probe per origin (single-flight), got %d", got)
	}
}

// TestIsWindowsReservedDeviceCandidateGuardsFalsePositive locks in the fix for
// a live false positive found via the H_NUL primitive research: bare "NUL" (any
// depth, any position) reads as a MANAGED-pipeline hit to IIS's routing — the
// exact signal dirAliasNative uses to confirm a real directory — so both
// --dir-confirm and the automatic [DIR] annotation would otherwise report the
// Win32 null-device namespace as a real filesystem directory. Verified live: CON/
// PRN/AUX/COM1-9/LPT1-9 do NOT currently reproduce the anomaly on the lab build,
// but are guarded too since the underlying mechanism (Win32 device namespace) is
// shared and could easily extend to them on a different build/config.
func TestIsWindowsReservedDeviceCandidateGuardsFalsePositive(t *testing.T) {
	positive := []string{"NUL", "nul", "Nul", "NUL~1", "nul.txt", "CON", "con",
		"PRN", "AUX", "COM1", "com9", "LPT1", "lpt9~2.dll"}
	for _, n := range positive {
		if !isWindowsReservedDeviceCandidate(n) {
			t.Errorf("%q must be recognised as a reserved device name", n)
		}
	}
	negative := []string{"NULLABLE~1", "CONFID~1", "AUXILIARY~1", "SECRET~1.CON", "PUBLIS~1"}
	for _, n := range negative {
		if isWindowsReservedDeviceCandidate(n) {
			t.Errorf("%q merely CONTAINS a device-name substring, must NOT match", n)
		}
	}

	// End-to-end: even against a mock that ALWAYS answers managed (would
	// otherwise report every device name as a confirmed directory), the guard
	// must reject them before ever issuing the probe.
	managed := `<html><head><title>Resource cannot be found</title></head><body>404</body></html>`
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusNotFound, managed), nil
	})}
	defer func() { dirConfirmOracle = map[string]bool{} }()
	dirConfirmOracle = map[string]bool{}
	if autoDirConfirmDirectory(client, &httpStats{}, "http://iis.test/", "NUL") {
		t.Error("NUL must never be auto-confirmed as a directory, even against an always-managed mock")
	}
}
