package shortscan

import (
	"fmt"
	"os"
	"strings"
	"sync"
	"time"

	"github.com/fatih/color"
)

// progressBar renders a single self-updating status line on stderr so a long,
// output-quiet phase (the recursive enumeration, the recovery cascade) visibly
// shows it is alive: a spinner, the current phase, the BFS queue position, the
// directory being scanned, the live request count/rate from httpStats, and how
// many short names have been found. It is stderr-only and auto-disabled when
// output is redirected, piped, --quiet, or not human, so scripted/redirected
// runs stay byte-for-byte identical. No new dependency: the TTY gate reuses
// fatih/color's own detection (color.NoColor).
type progressBar struct {
	mu    sync.Mutex
	phase string
	dir   string
	done  int // BFS queue positions processed
	total int // queue positions known so far (grows as dirs are discovered)
	found int // confirmed short names
	st    *httpStats
	on    bool
	// Multi-host parallel mode (--parallel > 1 over several URLs): per-directory
	// phase/dir/queue churn from the concurrent Scans would flicker chaotically
	// between hosts every tick, so it is suppressed and the bar shows aggregate
	// host completion instead. reqs/rate/found stay aggregate either way.
	parallel   bool
	hostsDone  int
	hostsTotal int
	stopCh     chan struct{}
}

var progress = &progressBar{}

// progressActive reports whether a live status line should be drawn. color.NoColor
// is false only when stdout is a colour-capable TTY, the same condition under
// which a self-updating stderr line is wanted.
func progressActive() bool {
	return args.Output == "human" && !args.Quiet && outputWriter == os.Stdout && !color.NoColor
}

// start begins the status line (inert no-op stop when inactive); use
// `defer progress.start(st)()`.
func (p *progressBar) start(st *httpStats) func() {
	if !progressActive() {
		return func() {}
	}
	p.mu.Lock()
	p.st = st
	p.on = true
	p.phase = "scanning"
	p.stopCh = make(chan struct{})
	fmt.Fprint(os.Stderr, "\033[?25l") // hide the cursor so its block does not sit on the gap line
	p.mu.Unlock()
	go p.loop()
	return p.stop
}

func (p *progressBar) stop() {
	p.mu.Lock()
	defer p.mu.Unlock()
	if !p.on {
		return
	}
	p.on = false
	close(p.stopCh)
	fmt.Fprint(os.Stderr, "\033[J\033[?25h") // erase the footer and restore the cursor
}

// setParallel switches the bar into multi-host mode. Called once from Run before
// the concurrent Scans launch, so the per-directory setters below become no-ops.
func (p *progressBar) setParallel(totalHosts int) {
	p.mu.Lock()
	p.parallel = true
	p.hostsTotal = totalHosts
	p.phase = "scanning"
	p.mu.Unlock()
}

func (p *progressBar) incHostDone() { p.mu.Lock(); p.hostsDone++; p.mu.Unlock() }

func (p *progressBar) setPhase(phase string) {
	p.mu.Lock()
	if !p.parallel {
		p.phase = phase
	}
	p.mu.Unlock()
}
func (p *progressBar) setDir(dir string) {
	p.mu.Lock()
	if !p.parallel {
		p.dir = dir
	}
	p.mu.Unlock()
}
func (p *progressBar) setQueue(done, total int) {
	p.mu.Lock()
	if !p.parallel {
		p.done, p.total = done, total
	}
	p.mu.Unlock()
}
func (p *progressBar) incFound() { p.mu.Lock(); p.found++; p.mu.Unlock() }

// write runs a stdout emit (a printHuman line) serialised against the footer:
// it erases the footer from its parked top, emits the line (whose trailing
// newline lands the cursor at the new footer top), and the next tick redraws
// the footer below. Holding the mutex across the emit keeps the redraw goroutine
// from interleaving cursor moves with the output. No-op decoration when inactive.
func (p *progressBar) write(emit func()) {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.on {
		fmt.Fprint(os.Stderr, "\033[J")
	}
	emit()
}

func (p *progressBar) loop() {
	spin := []rune("⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏")
	ticker := time.NewTicker(120 * time.Millisecond)
	defer ticker.Stop()
	i := 0
	lastReq := 0
	last := time.Now()
	for {
		select {
		case <-p.stopCh:
			return
		case <-ticker.C:
			p.mu.Lock()
			on, st := p.on, p.st
			phase, dir := p.phase, p.dir
			done, total, found := p.done, p.total, p.found
			parallel, hostsDone, hostsTotal := p.parallel, p.hostsDone, p.hostsTotal
			p.mu.Unlock()
			if !on {
				return
			}
			reqs := 0
			if st != nil {
				st.Lock()
				reqs = st.requests
				st.Unlock()
			}
			now := time.Now()
			rate := 0.0
			if d := now.Sub(last).Seconds(); d > 0 {
				rate = float64(reqs-lastReq) / d
			}
			lastReq, last = reqs, now

			var b strings.Builder
			fmt.Fprintf(&b, "%c %s", spin[i%len(spin)], phase)
			if parallel {
				// Aggregate host completion instead of the per-directory churn.
				fmt.Fprintf(&b, " [%d/%d hosts]", hostsDone, hostsTotal)
			} else {
				if total > 0 {
					fmt.Fprintf(&b, " [%d/%d]", done, total)
				}
				if dir != "" {
					fmt.Fprintf(&b, " %s", dir)
				}
			}
			// Live metrics grouped at the end: · (N found - N reqs X/s)
			b.WriteString(" · (")
			if found > 0 {
				fmt.Fprintf(&b, "%d found - ", found)
			}
			fmt.Fprintf(&b, "%d reqs %.0f/s)", reqs, rate)
			i++
			p.mu.Lock()
			if p.on {
				// 2-line footer: erase from the parked top, leave a blank gap line,
				// write the status on the next line, then park back on the (blank)
				// gap line so a stdout write pushes the whole footer down together.
				fmt.Fprintf(os.Stderr, "\033[J\n%s\033[1A\r", clampLine(b.String()))
			}
			p.mu.Unlock()
		}
	}
}

// clampLine keeps the status line within the terminal width (best-effort via
// $COLUMNS). Rune-sliced so the multibyte spinner is never cut mid-rune.
func clampLine(s string) string {
	w := 120
	if c := os.Getenv("COLUMNS"); c != "" {
		fmt.Sscanf(c, "%d", &w)
	}
	if w < 10 {
		w = 10
	}
	if r := []rune(s); len(r) > w-1 {
		return string(r[:w-1])
	}
	return s
}
