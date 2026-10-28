package shortscan

import (
	"net/http"
	"strings"
	"sync"

	"github.com/fatih/color"
)

// Wildcard-free directory 8.3-alias confirmation oracle.
//
// The classic tilde oracle needs the `*` wildcard (`/*a*~1*/`), which is the first
// thing a WAF strips. This oracle needs no wildcard at all. On IIS + ASP.NET a
// DIRECT GET of a full 8.3 short name behaves differently by pipeline:
//
//   * a REAL directory alias (e.g. /CONFID~1 where "ConfidentialArea" exists)
//     resolves and is rendered by the MANAGED pipeline -> an ASP.NET 404 with no
//     substatus and no physical path;
//   * a nonexistent short name -> the NATIVE IIS detailed 404.0 (substatus +
//     "Physical Path" present);
//   * a real FILE alias -> the native 404.0 too (so this only confirms DIRECTORIES).
//
// It is confirmation-only: it verifies a fully-known directory 8.3 name without a
// wildcard (handy where `*`/`?` are filtered, or the wildcard oracle is patched),
// but it cannot enumerate — `?`/`*` do not combine with the managed-vs-native
// signal. The distinction between the managed and native 404 is read with the same
// parseIISDetail() the fingerprinter uses, so it is locale-independent (it keys on
// the presence of an IIS substatus, not on a body length or a page string).
//
// NOTE: this is a refinement inside Soroush Dalili's 2023 "compare the whole
// response" principle, not a new oracle class — the delta is the specific
// managed-vs-native 404 signal and the directory-only routing, unimplemented in
// other tools.

// windowsReservedDeviceNames are the Win32 device namespace names that Windows
// intercepts specially regardless of directory context (CreateFile/GetFileAttributes
// on "anything\NUL" opens the null device rather than doing a real filesystem
// lookup). Found live: a bare "nul" path segment — ANY depth, ANY position, even
// mid-path with real segments following — makes IIS treat the request as a
// plausibly-real resource and hand it to the ASP.NET MANAGED pipeline instead of
// native-rejecting it, which is EXACTLY the signal dirAliasNative/dirconfirm use to
// confirm a real directory alias. Without this guard, --dir-confirm and the
// automatic [DIR] annotation both false-positive "NUL" as a real directory 8.3
// alias — it's the OS device namespace, not a filesystem entry. CON/PRN/AUX/
// COM1-9/LPT1-9 were tested too and do NOT reproduce this on the current lab
// build (only NUL does), but all are excluded here since the underlying Win32
// device-namespace mechanism is shared and a future build/config could easily
// extend the anomaly to the others.
var windowsReservedDeviceNames = map[string]bool{
	"CON": true, "PRN": true, "AUX": true, "NUL": true,
	"COM1": true, "COM2": true, "COM3": true, "COM4": true, "COM5": true,
	"COM6": true, "COM7": true, "COM8": true, "COM9": true,
	"LPT1": true, "LPT2": true, "LPT3": true, "LPT4": true, "LPT5": true,
	"LPT6": true, "LPT7": true, "LPT8": true, "LPT9": true,
}

// isWindowsReservedDeviceCandidate reports whether a short-name candidate's stem
// (before any "~N" ordinal or extension) is a Win32 reserved device name. Case-
// insensitive, since the device-namespace interception is (Windows paths always
// are).
func isWindowsReservedDeviceCandidate(name string) bool {
	stem := strings.ToUpper(name)
	if i := strings.IndexByte(stem, '~'); i >= 0 {
		stem = stem[:i]
	} else if i := strings.IndexByte(stem, '.'); i >= 0 {
		stem = stem[:i]
	}
	return windowsReservedDeviceNames[stem]
}

// dirAliasNative does a direct (wildcard-free) GET of a short name and reports
// whether the response is the NATIVE IIS detailed error (substatus present) rather
// than a managed 404. ok is false only if the host is unreachable.
func dirAliasNative(hc *http.Client, st *httpStats, base, name string) (status int, native bool, ok bool) {
	url := strings.TrimRight(base, "/") + "/" + strings.TrimPrefix(name, "/")
	code, version, substatus, _, res := fingerprintProbe(hc, st, "GET", url)
	if res == nil {
		return 0, false, false
	}
	return code, version != "" || substatus != "", true
}

// runDirConfirm drives --dir-confirm: per base URL it calibrates against a random
// fake short name (which MUST render the native detailed 404, else the oracle is
// unavailable), then reports which candidate names are real DIRECTORY 8.3 aliases,
// confirmed WITHOUT the `*` wildcard.
func runDirConfirm(bases []string, names []string, hc *http.Client, st *httpStats) {
	// split comma-separated groups and drop empties
	var cand []string
	for _, n := range names {
		for _, part := range strings.Split(n, ",") {
			if part = strings.TrimSpace(part); part != "" {
				cand = append(cand, part)
			}
		}
	}
	for _, base := range bases {
		printHuman(color.New(color.FgWhite, color.Bold).Sprint("[DIR-CONFIRM] "), base)

		fake := safeFakeShort()
		fstatus, fnative, fok := dirAliasNative(hc, st, base, fake)
		if !fok {
			printHuman(color.HiBlackString("    unreachable"))
			continue
		}
		if fstatus != 404 || !fnative {
			printHuman(color.HiBlackString("    oracle unavailable: fake %q -> status %d native=%v; the target does not render the native IIS detailed 404 (custom errors on, or not IIS) so the managed-vs-native signal can't be used", fake, fstatus, fnative))
			continue
		}
		printHuman(color.HiBlackString("    calibrated: fake %q -> native 404.0 (managed-vs-native oracle usable)", fake))

		for _, name := range cand {
			if isWindowsReservedDeviceCandidate(name) {
				printHuman(color.HiYellowString("    %-22s skipped — a Win32 reserved device name (CON/PRN/AUX/NUL/COM*/LPT*) always reads as a phantom managed-pipeline hit here, regardless of whether it's a real alias", name))
				continue
			}
			status, native, ok := dirAliasNative(hc, st, base, name)
			switch {
			case !ok:
				printHuman(color.HiBlackString("    %-22s unreachable", name))
			case status == 404 && !native:
				printHuman(color.HiGreenString("    %-22s -> real DIRECTORY 8.3 alias (managed 404, wildcard-free)", name))
			case status/100 == 2 || status == 301 || status == 302:
				printHuman(color.HiYellowString("    %-22s -> resolves (status %d) — real name (dir w/ default doc, or a file)", name, status))
			default:
				printHuman(color.HiBlackString("    %-22s -> not a directory alias (status %d, native=%v)", name, status, native))
			}
		}
	}
}

// dirConfirmOracle caches, per origin, whether the managed-vs-native 404 signal
// is usable at all (calibrated once against a fake name) — mirrors the
// fingerprintDone/singleStackHosts per-origin cache pattern elsewhere in this
// package, so a scan pays the one calibration probe once, not per candidate.
var (
	dirConfirmOracleMu sync.Mutex
	dirConfirmOracle   = map[string]bool{}      // origin -> oracle usable
	dirConfirmOnce     = map[string]*sync.Once{} // origin -> single-flight calibration
)

// autoDirConfirmDirectory reports whether an UNRESOLVED, extensionless short
// name (the "PUBLIS~1 -> PUBLIS?" case: the wordlist has no match, so the tool
// would otherwise say nothing about it) is a real DIRECTORY, using dirAliasNative
// — the SAME wildcard-free, HTTP-cheap technique --dir-confirm already exposes
// manually, now applied automatically during normal enumeration instead of
// requiring the operator to already suspect a candidate and re-run with the
// flag by hand. Lazily calibrates once per origin (a fake ~9 name MUST render
// the native detailed 404.0, else the signal isn't available on this target —
// custom errors on, or not IIS) and caches the verdict, so this costs one extra
// request per origin plus one per genuinely-unresolved extensionless name, never
// more. Returns false (silently) whenever the oracle isn't usable, unreachable,
// or the name isn't confirmably a directory — this only ever ADDS a positive
// "[DIR]" annotation, never removes information the rest of the pipeline found.
func autoDirConfirmDirectory(hc *http.Client, st *httpStats, base, name string) bool {
	if isWindowsReservedDeviceCandidate(name) {
		return false
	}
	origin := schemeHost(base)
	// Single-flight the calibration per origin: concurrent enumerate workers on the
	// same host otherwise each observe !calibrated and fire their own fake-name
	// probe. sync.Once makes exactly one run the calibration while the rest block on
	// it, honouring the "one calibration probe, once per origin" invariant.
	dirConfirmOracleMu.Lock()
	once, ok := dirConfirmOnce[origin]
	if !ok {
		once = &sync.Once{}
		dirConfirmOnce[origin] = once
	}
	dirConfirmOracleMu.Unlock()
	once.Do(func() {
		fstatus, fnative, fok := dirAliasNative(hc, st, base, safeFakeShort())
		dirConfirmOracleMu.Lock()
		dirConfirmOracle[origin] = fok && fstatus == 404 && fnative
		dirConfirmOracleMu.Unlock()
	})
	dirConfirmOracleMu.Lock()
	usable := dirConfirmOracle[origin]
	dirConfirmOracleMu.Unlock()
	if !usable {
		return false
	}
	status, native, ok := dirAliasNative(hc, st, base, name)
	return ok && status == 404 && !native
}

// safeFakeShort builds an 8.3-shaped short name that is almost certainly absent
// (an improbable stem with the ~9 ordinal, which effectively never exists).
func safeFakeShort() string {
	r := strings.ToUpper(fpRand())
	var b strings.Builder
	for _, c := range r {
		if (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') {
			b.WriteRune(c)
		}
	}
	stem := ("ZQ" + b.String() + "XXXX")
	return stem[:6] + "~9"
}
