package shortscan

import (
	"bytes"
	"strings"
	"testing"
)

func TestConsoleSummaryKeepsCaveats(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	args = arguments{Output: "human"}
	var out bytes.Buffer
	outputWriter = &out
	fp := fingerprintOutput{Url: "https://example.test/", TildeOracle: true,
		CrossStack: "interesting — shared tier", WebDAV: "not advertised",
		ADSFilterBypass: "inconclusive (detailed errors off)",
		Cookieless:      "same miss status (404) — inconclusive without a known existing path"}
	printFingerprintHuman(fp)
	printResultLegend([]string{"name [group match]", "web.config? [candidate; filtered]"})
	for _, want := range []string{"file access not confirmed", "DAV:not advertised", "alias unverified", "not confirmed; request-filtered, no direct GET", "-v 1"} {
		if !strings.Contains(out.String(), want) {
			t.Errorf("missing %q: %s", want, out.String())
		}
	}
	if strings.Contains(out.String(), "same miss status") {
		t.Fatal("default fingerprint retained inconclusive detail")
	}
	out.Reset()
	args.Verbosity = 1
	printFingerprintHuman(fp)
	if !strings.Contains(out.String(), "same miss status") {
		t.Fatal("verbose fingerprint lost detail")
	}
}

func TestQuietCrawlPreservesStructuredRecordsAndErrors(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	var out bytes.Buffer
	outputWriter = &out
	args = arguments{Output: "human"}
	reportReferenceCrawl(&attackConfig{}, referenceCrawlStats{pages: 1}, "initial")
	if out.Len() != 0 {
		t.Fatalf("empty crawl summary: %s", out.String())
	}
	reportReferenceCrawl(&attackConfig{}, referenceCrawlStats{pages: 1, errors: 1}, "initial")
	if !strings.Contains(out.String(), "1 error") {
		t.Fatal("crawl error hidden")
	}
	out.Reset()
	args.Output = "json"
	reportReferenceCrawl(&attackConfig{}, referenceCrawlStats{pages: 1}, "initial")
	if !strings.Contains(out.String(), "reference-statistics") {
		t.Fatal("structured crawl record lost")
	}
}

func TestActiveModesStayOnOneLine(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	defer func() { args, outputWriter = previousArgs, previousWriter }()
	args = arguments{Output: "human"}
	var out bytes.Buffer
	outputWriter = &out
	modes := []string{strings.Repeat("a", 50), strings.Repeat("b", 50), "retrieve"}
	printModeLines("Active:", modes)
	if strings.Count(out.String(), "\n") != 1 {
		t.Fatalf("unexpected wrapping: %q", out.String())
	}
	for _, mode := range modes {
		if !strings.Contains(out.String(), mode) {
			t.Fatalf("lost mode %q", mode)
		}
	}
}
