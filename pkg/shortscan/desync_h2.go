package shortscan

import (
	"bytes"
	"crypto/tls"
	"fmt"
	"net"
	"strings"
	"time"

	"github.com/fatih/color"
	"golang.org/x/net/http2"
	"golang.org/x/net/http2/hpack"
)

// HTTP/2 origin-side leniency probe (h2->h1 downgrade-desync preconditions).
//
// http.sys canonicalizes the URL path identically for h1 and h2, but its h2
// FRAME/HEADER layer accepts several RFC 9113-illegal inputs and forwards them to
// the worker (a normal :status) instead of a stream error. Each accepted input is
// a downgrade-desync precondition: a front end (WAF/CDN/LB) that terminates h2 and
// re-serializes to HTTP/1.1 for the IIS backend — or IIS/ARR acting as the h2 front
// end to an h1 backend — turns them into request-line / header splits. The
// standout is a bare SPACE (or TAB) in :path, which is illegal in an HTTP/1.1
// request target and fractures `GET /a b HTTP/1.1` on downgrade.
//
// HONEST SCOPE: these are ORIGIN-side observations. Single-stack they are inert
// (the worker returns a normal status). A complete smuggle needs a real downgrader
// in front — test against it. http.sys correctly REJECTS CR/LF/NUL in header
// values and in :path, so the classic header-injection vectors are closed.

type h2Case struct {
	label     string
	fields    []hpack.HeaderField
	control   bool // the valid baseline: MUST be accepted or the probe is unusable
	dangerous bool // an RFC-illegal input whose acceptance is a downgrade precondition
}

func h2Fields(host, path string, extra ...hpack.HeaderField) []hpack.HeaderField {
	f := []hpack.HeaderField{
		{Name: ":method", Value: "GET"},
		{Name: ":scheme", Value: "https"},
		{Name: ":authority", Value: host},
		{Name: ":path", Value: path},
	}
	return append(f, extra...)
}

func h2Cases(host string) []h2Case {
	return []h2Case{
		{"baseline (valid h2)", h2Fields(host, "/"), true, false},
		{"space in :path (h1-illegal — splits the request line on downgrade)", h2Fields(host, "/shortscan probe"), false, true},
		{"tab in :path", h2Fields(host, "/shortscan\tprobe"), false, true},
		{"uppercase header NAME (defeats a case-sensitive downstream filter)", h2Fields(host, "/", hpack.HeaderField{Name: "X-Shortscan-Probe", Value: "1"}), false, true},
		{"pseudo-header after a regular header", []hpack.HeaderField{
			{Name: ":method", Value: "GET"}, {Name: "x-shortscan", Value: "1"},
			{Name: ":scheme", Value: "https"}, {Name: ":authority", Value: host}, {Name: ":path", Value: "/"}}, false, true},
		{"te: chunked (RFC: only \"trailers\")", h2Fields(host, "/", hpack.HeaderField{Name: "te", Value: "chunked"}), false, true},
	}
}

var errNoH2 = &h2Error{"server did not negotiate HTTP/2 (ALPN h2)"}

type h2Error struct{ s string }

func (e *h2Error) Error() string { return e.s }

// desyncH2Detect runs the h2 leniency cases and returns the labels that actually
// REACHED THE ORIGIN (RFC-illegal inputs the endpoint forwarded), WITHOUT printing.
// Inputs the front end rejects itself (error status, no `via`) are excluded as
// benign, so a CDN/WAF/LB-fronted target that sanitises at the edge returns empty
// and --auto stays quiet. Empty also if h2 isn't negotiated or the baseline fails.
func desyncH2Detect(host, hostPort string) []string {
	cases := h2Cases(host)
	baseStatus, _, _, err := h2ProbeVia(hostPort, host, cases[0].fields)
	if err != nil || baseStatus == "" {
		return nil
	}
	var reached []string
	for _, c := range cases {
		if c.control {
			continue
		}
		status, via, frontEnd, e := h2ProbeVia(hostPort, host, c.fields)
		if e != nil || status == "" {
			continue // error / rejected at the h2 layer
		}
		if via == "" && frontEnd {
			continue // the front end rejected it — benign
		}
		reached = append(reached, c.label)
	}
	return reached
}

// runH2DesyncProbe drives the HTTP/2 side of --desync-probe for an https origin.
// Every case is classified with the `via`-header discriminator so the per-line
// output stays consistent with the final verdict: an RFC-illegal input that draws a
// FRONT-END-generated error (no `via`) is benign (the edge rejected it), while one
// that reaches the ORIGIN is a genuine precondition. The space-in-:path split test
// is the authoritative, prominently-reported result.
func runH2DesyncProbe(host, hostPort string) {
	cases := h2Cases(host)
	// baseline — establishes reachability and the origin's `via` signature.
	baseStatus, baseVia, _, err := h2ProbeVia(hostPort, host, cases[0].fields)
	if err != nil {
		printHuman(color.HiBlackString("    h2: %v (no HTTP/2 leniency probe)", err))
		return
	}
	if baseStatus == "" {
		printHuman(color.HiBlackString("    h2: baseline rejected at the h2 layer — cannot probe leniencies"))
		return
	}
	fronted := baseVia != ""
	edge := "the origin"
	if fronted {
		edge = "a front end (via seen) → IIS backend"
	}
	printHuman(color.HiBlackString("    h2 baseline: reached %s (status %s%s)", edge, baseStatus, viaTag(baseVia)))

	var reachedOrigin []string // dangerous inputs that actually reached the origin
	for _, c := range cases {
		if c.control {
			continue
		}
		status, via, frontEnd, err := h2ProbeVia(hostPort, host, c.fields)
		switch {
		case err != nil:
			printHuman(color.HiBlackString("    %-52s -> error: %v", c.label, err))
		case status == "":
			printHuman(color.HiBlackString("    %-52s -> rejected at the h2 layer (RST/GOAWAY) — safe", c.label))
		case via == "" && frontEnd:
			// error status, no `via`, non-backend body → the edge itself rejected it.
			printHuman(color.HiGreenString("    %-52s -> rejected by the front end (status %s, no via) — benign", c.label, status))
		default:
			reachedOrigin = append(reachedOrigin, c.label)
			printHuman(color.HiRedString("    %-52s -> REACHED ORIGIN (status %s%s) <<< RFC 9113-illegal accepted downstream", c.label, status, viaTag(via)))
		}
	}

	// Authoritative split test for space-in-:path (the only case that yields a
	// request-line split). Reported prominently regardless of the per-case guess.
	verdict, detail := h2ConfirmPathSplit(host, hostPort)
	// A status differential proves only that the illegal :path was handled
	// differently. It does not prove that an h2 front end reserialized it into an
	// HTTP/1.1 request line, so only a future marker-based end-to-end proof may use
	// the confirmed-split verdict.
	splitConfirmed := verdict == "confirmed-split"
	switch verdict {
	case "confirmed-split":
		printHuman(color.HiRedString("    [H2->H1 SPLIT] %s — %s", verdict, detail))
		printHuman(color.HiRedString("    A paired marker proved that the illegal :path became a second HTTP/1.1 request."))
	case "front-end-rejected":
		printHuman(color.HiGreenString("    [H2->H1 SPLIT] front-end-rejected (BENIGN) — %s", detail))
	case "backend-error-differential", "status-differential":
		printHuman(color.HiYellowString("    [H2->H1 SPLIT] %s — %s", verdict, detail))
		printHuman(color.HiBlackString("    Differential only: this does not prove an h2→h1 downgrade or request-line split."))
	default:
		printHuman(color.HiBlackString("    [H2->H1 SPLIT] %s — %s", verdict, detail))
	}

	// Single, honest final verdict.
	switch {
	case splitConfirmed:
		printHuman(color.HiRedString("    [H2 DESYNC] CRITICAL — an h2→h1 request-line split is confirmed against the IIS backend."))
	case len(reachedOrigin) > 0:
		printHuman(color.HiYellowString("    [H2 DESYNC] PRECONDITION — %d RFC 9113-illegal input(s) reach the origin over h2: %s.", len(reachedOrigin), strings.Join(h2ShortLabels(reachedOrigin), ", ")))
		if fronted {
			printHuman(color.HiBlackString("    A front end terminates h2 yet forwards these; exploitable only if it reserializes them raw into the h1 request (space-in-:path did not split here — see above)."))
		} else {
			printHuman(color.HiBlackString("    No front end detected (no via) — this is the origin's own h2 leniency, inert single-stack; a desync only behind an h2-terminating proxy that forwards to an h1 backend."))
		}
	default:
		printHuman(color.HiGreenString("    [H2] SAFE — the h2 endpoint rejects/sanitizes every RFC-illegal input; none reaches the backend."))
	}
}

// h2ShortLabel drops a case label's explanatory parenthetical for the compact
// summary line where several case names get joined into one line — the "(...)"
// detail is only worth its width next to that case's own per-line result.
func h2ShortLabel(label string) string {
	if idx := strings.Index(label, " ("); idx != -1 {
		return label[:idx]
	}
	return label
}

// h2ShortLabels applies h2ShortLabel to every label, for a compact joined summary.
func h2ShortLabels(labels []string) []string {
	short := make([]string, len(labels))
	for i, l := range labels {
		short[i] = h2ShortLabel(l)
	}
	return short
}

// anyContains reports whether any string in ss contains sub.
func anyContains(ss []string, sub string) bool {
	for _, s := range ss {
		if strings.Contains(s, sub) {
			return true
		}
	}
	return false
}

// h2ProbeVia opens one ALPN-h2 connection, sends the fields as a HEADERS frame, and
// returns the response `:status` ("" on RST_STREAM/GOAWAY), the `via` header, and a
// heuristic for whether the response was generated by the FRONT END itself (an error
// status, no `via`, body not IIS's) rather than proxied from the origin. This lets
// every case — and the split test — tell a real BACKEND result from a benign
// FRONT-END rejection of the illegal char (the LB sanitised it before the backend).
func h2ProbeVia(hostPort, serverName string, fields []hpack.HeaderField) (status, via string, frontEnd bool, err error) {
	countDesyncProbe()
	delayRequest() // raw-socket probe: still bound by --rate like every fetch()-based request
	conn, err := tls.DialWithDialer(&net.Dialer{Timeout: 8 * time.Second}, "tcp", hostPort, &tls.Config{
		InsecureSkipVerify: true, // #nosec G402 — read-only desync precondition probe
		NextProtos:         []string{"h2"},
		ServerName:         serverName,
	})
	if err != nil {
		return "", "", false, err
	}
	defer conn.Close()
	if cs := conn.ConnectionState(); cs.NegotiatedProtocol != "h2" {
		return "", "", false, errNoH2
	}
	_ = conn.SetDeadline(time.Now().Add(8 * time.Second))
	if _, err = conn.Write([]byte(http2.ClientPreface)); err != nil {
		return "", "", false, err
	}
	fr := http2.NewFramer(conn, conn)
	fr.AllowIllegalWrites = true
	if err = fr.WriteSettings(); err != nil {
		return "", "", false, err
	}
	var buf bytes.Buffer
	enc := hpack.NewEncoder(&buf)
	for _, f := range fields {
		_ = enc.WriteField(f)
	}
	if err = fr.WriteHeaders(http2.HeadersFrameParam{
		StreamID: 1, BlockFragment: buf.Bytes(), EndStream: true, EndHeaders: true,
	}); err != nil {
		return "", "", false, err
	}
	var body []byte
	got := false
	for {
		f, e := fr.ReadFrame()
		if e != nil {
			break
		}
		done := false
		switch v := f.(type) {
		case *http2.HeadersFrame:
			dec := hpack.NewDecoder(4096, nil)
			hf, _ := dec.DecodeFull(v.HeaderBlockFragment())
			for _, h := range hf {
				switch h.Name {
				case ":status":
					status = h.Value
					got = true
				case "via":
					via = h.Value
				}
			}
			if v.StreamEnded() {
				done = true
			}
		case *http2.DataFrame:
			body = append(body, v.Data()...)
			if len(body) > 2048 || v.StreamEnded() {
				done = true
			}
		case *http2.RSTStreamFrame, *http2.GoAwayFrame:
			done = true
		case *http2.SettingsFrame:
			if !v.IsAck() {
				_ = fr.WriteSettingsAck()
			}
		}
		if done {
			break
		}
	}
	if !got {
		return "", "", false, nil
	}
	low := bytes.ToLower(body)
	isErr := len(status) > 0 && (status[0] == '4' || status[0] == '5')
	looksBackend := bytes.Contains(low, []byte("asp.net")) || bytes.Contains(low, []byte("iis")) ||
		bytes.Contains(low, []byte("file or directory"))
	// front-end-generated error: an error status, no `via` (never proxied), body not IIS's.
	frontEnd = isErr && via == "" && !looksBackend
	return status, via, frontEnd, nil
}

// h2ConfirmPathSplit tests whether an accepted space in :path actually reaches the
// backend differently versus being rejected by the front end. It compares a clean
// nonexistent path against the same path + " HTTP/1.1", using the `via` header
// and error-body source to classify the differential conservatively:
//   - space path answered by the FRONT END (front-end error, no `via`, while the
//     clean path reached the origin) → the LB sanitised the char → benign, NO split.
//   - space path reached the origin and changed status → precondition only. Status
//     cannot prove that an h2-to-h1 conversion or request-line split occurred.
//
// This avoids the false positive where a CDN/WAF/LB's own 400 (rejecting the illegal
// char) is mistaken for a backend request-line split. Read-only (nonexistent paths).
func h2ConfirmPathSplit(host, hostPort string) (verdict, detail string) {
	r := fpRand()
	stP, viaP, feP, ep := h2ProbeVia(hostPort, host, h2Fields(host, "/shortscanNX"+r))
	stS, viaS, feS, es := h2ProbeVia(hostPort, host, h2Fields(host, "/shortscanNX"+r+" HTTP/1.1"))
	if ep != nil || es != nil || stP == "" || stS == "" {
		return "inconclusive", "endpoint dropped a probe"
	}
	detail = fmt.Sprintf("/nx -> %s%s ; /nx<space>HTTP/1.1 -> %s%s", stP, viaTag(viaP), stS, viaTag(viaS))
	// The clean path reached the origin but the space path was answered by the front
	// end → the front end rejected the illegal char itself. No downstream split.
	if feS && !feP {
		return "front-end-rejected", detail + " — the h2 front end rejected the space itself; it never reached the backend (benign, NOT a desync)"
	}
	return classifyH2PathDifferential(stP, stS, feP, feS, detail)
}

// classifyH2PathDifferential deliberately stops at a precondition. HTTP status
// alone cannot distinguish an h2-native rejection/application route from an
// h2-to-h1 request-line split; confirmation requires an observable marker request.
func classifyH2PathDifferential(stP, stS string, feP, feS bool, detail string) (string, string) {
	if feS && !feP {
		return "front-end-rejected", detail + " — the h2 front end rejected the space itself; it never reached the backend (benign, NOT a desync)"
	}
	if (stS == "400" || stS == "501" || stS == "505") && !feS {
		return "backend-error-differential", detail
	}
	if stS != stP && !feS {
		return "status-differential", detail
	}
	return "no-split (endpoint sanitized the space)", detail
}

func viaTag(via string) string {
	if via != "" {
		return " (via " + via + ")"
	}
	return " (no via)"
}

// h2HostPort derives host:443 for an https URL host that omits the port. Must
// use net.SplitHostPort rather than a bare ":" check: a bracketed IPv6 literal
// with no port (url.URL.Host gives "[::1]" for https://[::1]/) already contains
// colons from the address itself, so a ":" check wrongly treats it as already
// having a port and leaves it unbracketed-and-portless for the dialer.
func h2HostPort(u string) string {
	if _, _, err := net.SplitHostPort(u); err == nil {
		return u // already host:port (IPv4, hostname, or bracketed IPv6)
	}
	host := strings.TrimPrefix(strings.TrimSuffix(u, "]"), "[")
	return net.JoinHostPort(host, "443")
}
