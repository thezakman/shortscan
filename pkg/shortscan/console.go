package shortscan

import (
	"strings"

	"github.com/fatih/color"
)

// printModeLines wraps at mode boundaries instead of leaving a single long line.
func printModeLines(label string, modes []string) {
	const width = 88
	line := ""
	prefix := label + " "
	for _, mode := range modes {
		if line != "" && len(line)+len(mode)+3 > width {
			printHuman(prefix + color.HiCyanString(line))
			prefix, line = "        ", ""
		}
		if line != "" {
			line += " · "
		}
		line += mode
	}
	if line != "" {
		printHuman(prefix + color.HiCyanString(line))
	}
}

func printResultLegend(lines []string) {
	group, candidate := false, false
	for _, line := range lines {
		group = group || strings.Contains(line, "[group match]")
		candidate = candidate || strings.Contains(line, "[candidate; filtered]")
	}
	if group {
		printHuman(color.HiBlackString("  group match: long name recovered; association with this ~N alias unverified."))
	}
	if candidate {
		printHuman(color.YellowString("  candidate: inferred name, not confirmed; request-filtered, no direct GET."))
	}
	if group || candidate {
		printHuman(color.HiBlackString("  Details: -v 1 (method, collision group and provenance)."))
	}
}

// Keep actionable signals visible; routine inconclusive checks belong in -v 1.
func printFingerprintSummary(o fingerprintOutput) {
	printHuman()
	printHuman("Fingerprint: " + o.Url)
	printHuman("  " + fingerprintCompactLine(o))
	if strings.HasPrefix(o.CrossStack, "interesting") || strings.HasPrefix(o.CrossStack, "mixed") {
		printHuman(color.HiYellowString("  Cross-stack candidate: proxy or shared Windows tier; file access not confirmed."))
	}
	if o.ADSFilterBypass != "" && !strings.HasPrefix(o.ADSFilterBypass, "inconclusive") {
		printHuman("  ADS/filter: " + o.ADSFilterBypass)
	}
	if o.Cookieless != "" && !strings.Contains(o.Cookieless, "inconclusive") {
		printHuman("  Cookieless: " + o.Cookieless)
	}
	if o.CollapseMode != "" {
		printHuman("  Collapse: " + o.CollapseMode)
	}
	if o.PhysicalPath != "" {
		printHuman("  Physical path: " + o.PhysicalPath)
	}
	if len(o.Substatuses) > 0 {
		printHuman("  Substatus: " + strings.Join(o.Substatuses, " · "))
	}
	if o.WebDAV != "" && o.WebDAV != "not advertised" {
		printHuman("  WebDAV: " + o.WebDAV)
	}
	if o.AllowCopyOracle {
		printHuman("  allow-copy oracle available (--brute-oracle allow-copy)")
	}
	for _, note := range o.Notes {
		printHuman("  · " + note)
	}
	printHuman(color.HiBlackString("  Full fingerprint and inconclusive checks: -v 1"))
}
