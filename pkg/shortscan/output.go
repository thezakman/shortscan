package shortscan

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/fatih/color"
)

type resultOutput struct {
	Type                          string   `json:"type"`
	FullMatch                     bool     `json:"fullmatch"`
	Tentative                     bool     `json:"tentative,omitempty"`
	SourceDisclosure              bool     `json:"sourcedisclosure,omitempty"`
	DisclosureType                string   `json:"disclosuretype,omitempty"`
	BaseUrl                       string   `json:"baseurl"`
	File                          string   `json:"shortfile"`
	Ext                           string   `json:"shortext"`
	Tilde                         string   `json:"shorttilde"`
	Partname                      string   `json:"partname"`
	Fullname                      string   `json:"fullname"`
	MatchType                     string   `json:"matchtype,omitempty"`
	Status                        int      `json:"status,omitempty"`
	CollisionGroup                string   `json:"collisiongroup,omitempty"`
	OrdinalVerified               *bool    `json:"ordinalverified,omitempty"`
	AliasVerified                 *bool    `json:"aliasverified,omitempty"`
	LFNAssociationVerified        *bool    `json:"lfnassociationverified,omitempty"`
	CustomSFNCandidate            bool     `json:"customsfncandidate,omitempty"`
	CanonicalGuardBypassCandidate bool     `json:"canonicalguardbypasscandidate,omitempty"`
	Oracle                        string   `json:"oracle,omitempty"`
	Method                        string   `json:"method,omitempty"`
	ProbeSuffix                   string   `json:"probesuffix,omitempty"`
	Checksum                      string   `json:"checksum,omitempty"`
	DerivedFrom                   string   `json:"derivedfrom,omitempty"`
	CandidateFamilies             []string `json:"candidatefamilies,omitempty"`
	DetectionOracle               string   `json:"detectionoracle,omitempty"`
	DetectionMethod               string   `json:"detectionmethod,omitempty"`
	DetectionSuffix               string   `json:"detectionsuffix,omitempty"`
	DetectionStatus               int      `json:"detectionstatus,omitempty"`
	DirectoryConfirmed            bool     `json:"directoryconfirmed,omitempty"`
	SensitiveReason               string   `json:"sensitivereason,omitempty"`
}

type statusOutput struct {
	Type         string `json:"type"`
	Url          string `json:"url"`
	Server       string `json:"server"`
	Vulnerable   bool   `json:"vulnerable"`
	Oracle       string `json:"oracle,omitempty"`
	Method       string `json:"method,omitempty"`
	ProbeSuffix  string `json:"probesuffix,omitempty"`
	ProfileCount int    `json:"profilecount,omitempty"`
}

type fingerprintOutput struct {
	Type            string   `json:"type"`
	Url             string   `json:"url"`
	Server          string   `json:"server"`
	IISVersion      string   `json:"iisversion,omitempty"`
	AspNet          string   `json:"aspnet,omitempty"`
	AspNetMvc       string   `json:"aspnetmvc,omitempty"`
	PoweredBy       string   `json:"poweredby,omitempty"`
	DetailedErrors  bool     `json:"detailederrors"`
	Substatuses     []string `json:"substatuses,omitempty"`
	TildeOracle     bool     `json:"tildeoracle"`
	CrossStack      string   `json:"crossstack,omitempty"`
	ADSFilterBypass string   `json:"adsfilterbypass,omitempty"`
	Cookieless      string   `json:"cookieless,omitempty"`
	CollapseMode    string   `json:"collapsemode,omitempty"`
	PhysicalPath    string   `json:"physicalpath,omitempty"`
	WebDAV          string   `json:"webdav,omitempty"`
	AllowCopyOracle bool     `json:"allowcopyoracle"`
	Notes           []string `json:"notes,omitempty"`
}

type statsOutput struct {
	Type          string `json:"type"`
	Requests      int    `json:"requests"`
	Retries       int    `json:"retries"`
	SentBytes     int    `json:"sentbytes"`
	ReceivedBytes int    `json:"receivedbytes"`
}

// outputWriter is the destination for printHuman/printJSON; defaults to stdout.
// When --output-file is set, Run() replaces this with a file handle.
var outputWriter io.Writer = os.Stdout

// Per-host output buffering for --parallel human mode.
//
// When several URL scans run at once, line-interleaved human output is unreadable:
// a "[SHORTNAMES] FILE~1.TXT" line gives no hint which host it belongs to. So each
// scan's goroutine buffers its human output here and flushes the whole block
// atomically — host-labelled — the moment that scan finishes. Blocks from different
// hosts therefore never interleave line-by-line; they appear contiguous, in
// completion order, while the status bar shows aggregate [done/total hosts] live.
//
// This is safe because ALL printHuman output originates from the scan's own
// goroutine: every concurrent worker in a scan (char discovery, enumerate,
// fingerprint probes) collects/buffers its results and the main goroutine prints
// after Wait(). A goroutine-keyed sink therefore captures the entire block, and a
// scan's buffer is only ever touched by its own goroutine (no per-buffer lock
// needed — only the registry map is guarded).
//
// json/ndjson deliberately do NOT buffer: those records are self-contained (each
// carries its own url/baseurl) and stream better for piping. Only human buffers.
var (
	hostSinks      = map[int64]*hostSink{}
	hostSinkMu     sync.Mutex
	hostSinkActive int32 // atomic; nonzero only during a parallel-human run
)

type hostSink struct {
	mu        sync.Mutex
	host      string
	buf       strings.Builder
	footer    strings.Builder   // subordinate lines emitted AFTER the findings (e.g. the desync precondition), so a non-finding never leads the host block
	fp        fingerprintOutput // stashed so the compact header can render it as one line
	fpSet     bool
	headerSet bool
	closed    bool
}

// enableHostSinks arms per-host buffering (called once by Run for parallel human).
func enableHostSinks() { atomic.StoreInt32(&hostSinkActive, 1) }

// bulkCompact reports whether output should use the lean per-host bulk format
// (one-line header + one-line fingerprint + findings, no scaffolding). It is armed
// together with per-host buffering, so the two conditions always coincide.
func bulkCompact() bool { return atomic.LoadInt32(&hostSinkActive) != 0 }

// setHostFingerprint stashes the fingerprint struct for the calling scan so the
// compact per-host header renders it as a single line instead of an 8-line block.
func setHostFingerprint(o fingerprintOutput) {
	hostSinkMu.Lock()
	if s := hostSinks[goroutineID()]; s != nil {
		s.mu.Lock()
		s.fp, s.fpSet = o, true
		s.mu.Unlock()
	}
	hostSinkMu.Unlock()
}

// takeHostFingerprint returns and clears the stashed fingerprint for the caller.
func takeHostFingerprint() (fingerprintOutput, bool) {
	hostSinkMu.Lock()
	defer hostSinkMu.Unlock()
	s := hostSinks[goroutineID()]
	if s == nil {
		return fingerprintOutput{}, false
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if !s.fpSet || s.closed {
		return fingerprintOutput{}, false
	}
	s.fpSet = false
	return s.fp, true
}

// compactHostHeader renders the one-line per-host header for bulk-compact output:
// "──── <url> ─── VULNERABLE · <oracle>" or "──── <url> ─── not vulnerable [!]".
func compactHostHeader(url string, vulnerable bool, oracle string, flagged bool) string {
	rule := color.New(color.FgHiBlack).Sprint("────")
	var verdict string
	if vulnerable {
		verdict = color.HiRedString("VULNERABLE")
		if oracle != "" && oracle != "none" {
			verdict += color.HiBlackString(" · " + oracle)
		}
	} else {
		verdict = color.HiBlackString("not vulnerable")
		if flagged {
			verdict += " " + color.HiRedString("[!]")
		}
	}
	return fmt.Sprintf("%s %s %s %s", rule, url, rule, verdict)
}

// indentBulkBody indents every line of a flushed compact block except the first
// (the host header) by two spaces, giving the nested per-host look.
func indentBulkBody(block string) string {
	lines := strings.Split(strings.TrimRight(block, "\n"), "\n")
	var b strings.Builder
	for i, ln := range lines {
		if i > 0 && ln != "" {
			b.WriteString("  ")
		}
		b.WriteString(ln)
		b.WriteByte('\n')
	}
	return b.String()
}

// goroutineID returns the current goroutine's numeric id, parsed from the runtime
// stack header ("goroutine <id> [running]:"). Only used at the output funnel, which
// is far off the request hot path, and only while a parallel-human run is armed.
func goroutineID() int64 {
	var b [32]byte
	n := runtime.Stack(b[:], false)
	s := b[:n]
	s = s[len("goroutine "):]
	i := 0
	for i < len(s) && s[i] >= '0' && s[i] <= '9' {
		i++
	}
	id, _ := strconv.ParseInt(string(s[:i]), 10, 64)
	return id
}

// beginHostSink registers a buffer for the calling scan goroutine.
func beginHostSink(host string) {
	hostSinkMu.Lock()
	hostSinks[goroutineID()] = &hostSink{host: host}
	hostSinkMu.Unlock()
}

// flushHostSink emits the calling goroutine's buffered block atomically, with a
// dim host separator, then drops the buffer. No-op if nothing was buffered.
func flushHostSink() {
	id := goroutineID()
	hostSinkMu.Lock()
	sink := hostSinks[id]
	delete(hostSinks, id)
	hostSinkMu.Unlock()
	flushSink(sink, false)
}

// flushAllHostSinks drains every partial human block during SIGINT. Each sink has
// its own lock so this can safely race with the owning scan goroutine's last write.
func flushAllHostSinks() {
	hostSinkMu.Lock()
	sinks := make([]*hostSink, 0, len(hostSinks))
	for id, sink := range hostSinks {
		sinks = append(sinks, sink)
		delete(hostSinks, id)
	}
	hostSinkMu.Unlock()
	for _, sink := range sinks {
		flushSink(sink, true)
	}
}

func flushSink(sink *hostSink, interrupted bool) {
	if sink == nil {
		return
	}
	sink.mu.Lock()
	if sink.closed {
		sink.mu.Unlock()
		return
	}
	sink.closed = true
	if sink.buf.Len() == 0 && sink.footer.Len() == 0 {
		sink.mu.Unlock()
		return
	}
	// Footer lines (desync precondition, etc.) trail the findings so a non-finding
	// never becomes the block's leading line.
	block := sink.buf.String() + sink.footer.String()
	host := sink.host
	headerSet := sink.headerSet
	sink.mu.Unlock()
	if bulkCompact() {
		if interrupted && !headerSet {
			block = fmt.Sprintf("%s %s %s %s\n", color.New(color.FgHiBlack).Sprint("────"), host,
				color.New(color.FgHiBlack).Sprint("────"), color.HiYellowString("interrupted · partial results")) + block
		}
		// The block already opens with the compact "──── url ─── verdict" header,
		// so no separate host rule is needed — just a blank line between hosts and
		// a two-space indent for the body under the header.
		body := indentBulkBody(block)
		progress.write(func() { fmt.Fprintln(outputWriter); fmt.Fprint(outputWriter, body) })
		return
	}
	header := color.New(color.FgHiBlack).Sprintf("──────── %s ────────", host)
	progress.write(func() { fmt.Fprintln(outputWriter, header); fmt.Fprint(outputWriter, block) })
}

// currentSink returns the calling goroutine's buffer, or nil when unbuffered
// (serial runs skip goroutineID entirely via the atomic gate).
func currentSink() *hostSink {
	if atomic.LoadInt32(&hostSinkActive) == 0 {
		return nil
	}
	hostSinkMu.Lock()
	s := hostSinks[goroutineID()]
	hostSinkMu.Unlock()
	return s
}

// printHuman prints human-readable output if enabled (suppressed by --quiet for headers)
func printHuman(s ...any) {
	if args.Output != "human" {
		return
	}
	if sink := currentSink(); sink != nil {
		sink.mu.Lock()
		if !sink.closed {
			fmt.Fprintln(&sink.buf, s...)
			sink.mu.Unlock()
			return
		}
		sink.mu.Unlock()
	}
	progress.write(func() { fmt.Fprintln(outputWriter, s...) })
}

// printHumanHostHeader records that the compact block already has its normal
// per-host header. An early SIGINT can otherwise drain findings produced before
// Scan reaches the verdict header; flushSink adds an explicit partial header then.
func printHumanHostHeader(s string) {
	if args.Output != "human" {
		return
	}
	if sink := currentSink(); sink != nil {
		sink.mu.Lock()
		if !sink.closed {
			sink.headerSet = true
			fmt.Fprintln(&sink.buf, s)
			sink.mu.Unlock()
			return
		}
		sink.mu.Unlock()
	}
	progress.write(func() { fmt.Fprintln(outputWriter, s) })
}

// printHumanFooter emits subordinate lines that belong AFTER a host's findings
// rather than inline where they are computed. In a buffered (bulk) run they land in
// the sink's footer, so the desync precondition can never lead the host block or be
// mistaken for its header. Serial runs have no sink, so it falls back to printing in
// place (a single-host scan reads top-to-bottom anyway).
func printHumanFooter(s ...any) {
	if args.Output != "human" {
		return
	}
	if sink := currentSink(); sink != nil {
		sink.mu.Lock()
		if !sink.closed {
			fmt.Fprintln(&sink.footer, s...)
			sink.mu.Unlock()
			return
		}
		sink.mu.Unlock()
	}
	progress.write(func() { fmt.Fprintln(outputWriter, s...) })
}

// csvHeaderPrinted ensures the CSV header is emitted only once
var csvHeaderPrinted bool
var csvMutex sync.Mutex

// outputMu serialises json/ndjson lines so --parallel URL scans do not interleave
// mid-write on the shared output writer.
var outputMu sync.Mutex

// vulnerableCountMu guards the shared vulnerableCount increment across --parallel URL scans.
var vulnerableCountMu sync.Mutex

// printJSON prints structured output (json, ndjson, csv) if enabled
func printJSON(o any) {
	switch args.Output {
	case "json", "ndjson":
		j, _ := json.Marshal(o)
		outputMu.Lock()
		fmt.Fprintln(outputWriter, string(j))
		outputMu.Unlock()
	case "csv":
		csvMutex.Lock()
		defer csvMutex.Unlock()
		if !csvHeaderPrinted {
			fmt.Fprintln(outputWriter, "type,fullmatch,tentative,disclosure,disclosuretype,baseurl,shortfile,shortext,shorttilde,partname,fullname,matchtype,status,collisiongroup,ordinalverified,oracle,method,probesuffix,checksum,derivedfrom,candidatefamilies,aliasverified,lfnassociationverified,customsfncandidate,canonicalguardbypasscandidate,directoryconfirmed,sensitivereason")
			csvHeaderPrinted = true
		}
		if r, ok := o.(resultOutput); ok {
			ordinalVerified := ""
			if r.OrdinalVerified != nil {
				ordinalVerified = strconv.FormatBool(*r.OrdinalVerified)
			}
			aliasVerified := ""
			if r.AliasVerified != nil {
				aliasVerified = strconv.FormatBool(*r.AliasVerified)
			}
			lfnAssociationVerified := ""
			if r.LFNAssociationVerified != nil {
				lfnAssociationVerified = strconv.FormatBool(*r.LFNAssociationVerified)
			}
			fmt.Fprintf(outputWriter, "%s,%t,%t,%t,%q,%q,%q,%q,%q,%q,%q,%q,%d,%q,%q,%q,%q,%q,%q,%q,%q,%q,%q,%t,%t,%t,%q\n",
				r.Type, r.FullMatch, r.Tentative, r.SourceDisclosure, r.DisclosureType,
				r.BaseUrl, r.File, r.Ext, r.Tilde, r.Partname, r.Fullname, r.MatchType, r.Status,
				r.CollisionGroup, ordinalVerified, r.Oracle, r.Method, r.ProbeSuffix,
				r.Checksum, r.DerivedFrom, strings.Join(r.CandidateFamilies, "|"), aliasVerified,
				lfnAssociationVerified, r.CustomSFNCandidate, r.CanonicalGuardBypassCandidate,
				r.DirectoryConfirmed, r.SensitiveReason)
		} else {
			warnCSVDroppedRecordOnce()
		}
	}
}

var csvDroppedRecordWarned bool

// warnCSVDroppedRecordOnce tells the operator, once per run, that -o csv's fixed
// schema only carries resultOutput records — fingerprint/status/statistics/etc.
// records are silently unencodable into that schema otherwise, with nothing
// indicating they never made it into the file.
func warnCSVDroppedRecordOnce() {
	if csvDroppedRecordWarned {
		return
	}
	csvDroppedRecordWarned = true
	fmt.Fprintln(os.Stderr, "shortscan: note: -o csv carries only recovered/short-name result records; fingerprint, status, statistics, and other records are not written to the CSV (use json/ndjson for those)")
}

// printFinishedStats emits the common final counter record used by normal
// enumeration and standalone probe modes.
func printFinishedStats(st *httpStats) {
	st.Lock()
	requests, retries := st.requests, st.retries
	sent, received := st.bytesTx, st.bytesRx
	st.Unlock()

	printHuman()
	if atomic.LoadInt32(&maskTruncated) == 1 {
		printHuman(color.HiYellowString("Note: --checksum-mask hit --checksum-limit for at least one grammar; some names may be truncated. Narrow --checksum-alphabet/mask (fewer '?'/smaller alphabet) or raise --checksum-limit."))
	}
	printHuman(fmt.Sprintf("%s Requests: %d; Retries: %d; Sent %d bytes; Received %d bytes",
		color.New(color.FgWhite, color.Bold).Sprint("Finished!"), requests, retries, sent, received))
	printJSON(statsOutput{Type: "statistics", Requests: requests, Retries: retries, SentBytes: sent, ReceivedBytes: received})
}
