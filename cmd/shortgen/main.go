// shortgen — turn IIS 8.3 short-name fragments (from shortscan) into a candidate wordlist of
// full names, ready to feed back into `shortscan -w` or ffuf for HTTP confirmation.
//
// The 8.3 oracle only ever reveals 6 base chars + a 3-char (truncated) extension. shortgen
// closes that gap OFFLINE, using the real 8.3 algorithm (shortutil.Gen8dot3) for correctness:
//
//  1. Extension expansion — a 3-char 8.3 extension is a prefix of the real one, so every
//     plausible full extension whose 8.3 form matches is emitted (.CON->.config, .ASP->.aspx
//     /.asax/.ashx/…, .JSO->.json).
//  2. Complete-base pass — an 8.3 base < 6 chars is the WHOLE base (truncation always fills 6),
//     so the base is emitted as-is.
//  3. Wordlist completion (6-char bases) — words from -w whose 8.3 base equals the fragment
//     (CONFIG -> configuration, configure, …).
//  4. Separator compounding (6-char bases) — prefix + {"",-,_,.,space} + suffix-word, the way
//     real names truncate (SITEBA~1.ZIP -> site-backup.zip / site_backup.zip / sitebackup.zip).
//
// Input: fragments as args (WEB~1.CON) and/or shortscan output on stdin (fragments are scraped).
//
//	shortscan http://t/ | shortgen -w words.txt -o candidates.txt
//	shortgen APP_WE~1.DLL SITEBA~1.ZIP -o cands.txt
//	shortscan http://t/ -w candidates.txt      # confirm the generated names
package main

import (
	"bufio"
	"flag"
	"fmt"
	"io"
	"net/http"
	"os"
	"regexp"
	"sort"
	"strings"
	"time"

	"github.com/thezakman/shortscan/pkg/shortutil"
)

// Dynamic source: a recovered/reachable page references MORE real names, folders and the
// target's own naming convention (the "_" style, path layout). Scrape them and feed them
// back as candidates + wordlist. This is the closed loop: recover a file -> read it -> more
// names to (re)scan.
var (
	attrRe = regexp.MustCompile(`(?i)(?:href|src|action|data-src|data-url|url|content|poster|import|from)\s*[=(:]\s*["'` + "`" + `]?([^"'` + "`" + `()<>\s]+)`)
	strRe  = regexp.MustCompile(`["'` + "`" + `]([A-Za-z0-9_./\-]{2,}\.[A-Za-z0-9]{1,6})["'` + "`" + `]`)
)

// fetchNames pulls a URL and extracts candidate file/folder names (each path segment) from
// its references, preserving the target's own naming convention.
func fetchNames(u string, insecure bool, out map[string]bool) int {
	client := &http.Client{Timeout: 15 * time.Second}
	resp, err := client.Get(u)
	if err != nil {
		fmt.Fprintln(os.Stderr, "url:", u, err)
		return 0
	}
	defer resp.Body.Close()
	body, _ := io.ReadAll(io.LimitReader(resp.Body, 8<<20))
	text := string(body)
	n := 0
	add := func(ref string) {
		ref = strings.SplitN(ref, "?", 2)[0]
		ref = strings.SplitN(ref, "#", 2)[0]
		for _, seg := range strings.Split(ref, "/") {
			seg = strings.TrimSpace(seg)
			if len(seg) < 2 || len(seg) > 64 || seg == "." || seg == ".." || strings.ContainsAny(seg, ":\\*?\"<>|") {
				continue
			}
			if !out[seg] {
				out[seg] = true
				n++
			}
		}
	}
	for _, m := range attrRe.FindAllStringSubmatch(text, -1) {
		add(m[1])
	}
	for _, m := range strRe.FindAllStringSubmatch(text, -1) {
		add(m[1])
	}
	fmt.Fprintf(os.Stderr, "shortgen: %s -> %d names\n", u, n)
	return n
}

// A 3-char 8.3 extension is only a prefix; map it to every plausible full extension.
var knownExtensions = []string{
	"asp", "aspx", "asax", "ascx", "asmx", "ashx", "axd", "rem", "cs", "cshtml", "vb", "vbhtml", "razor", "svc", "compiled",
	"master", "sitemap", "browser", "resx", "resources", "dll", "pdb",
	"csproj", "vbproj", "sln", "nupkg", "snk", "licx", "edmx", "dbml",
	"php", "phtml", "php5", "php7", "jsp", "jspx", "cfm", "do", "action",
	"config", "settings", "cscfg", "publishsettings", "pubxml", "disco", "yaml", "yml", "toml", "ini", "env", "properties",
	"json", "xml", "wsdl", "xsd", "soap", "sql", "sqlite", "db", "mdf", "ldf", "csv", "xls", "xlsx", "doc", "docx",
	"html", "htm", "xhtml", "js", "mjs", "cjs", "ts", "tsx", "jsx", "vue", "css", "scss", "sass", "less", "map", "webmanifest",
	"wasm", "svg", "woff", "woff2", "ttf", "otf", "txt", "log", "md",
	"cer", "crt", "der", "pfx", "p12", "jks", "keystore", "key", "pem",
	"br", "gz", "zip", "7z", "rar", "bak", "backup", "old", "orig", "save", "tmp", "swp", "inc", "tpl", "lock",
}

// Common name tails / versions / environments for separator compounding.
var defaultSuffixes = []string{
	"bak", "backup", "old", "orig", "copy", "new", "final", "save", "tmp", "temp", "test", "dev", "prod", "staging", "live", "local",
	"1", "2", "3", "01", "02", "v1", "v2", "v3", "2020", "2021", "2022", "2023", "2024", "2025",
	"admin", "user", "data", "db", "sql", "dump", "export", "archive", "config", "secret", "internal", "manager", "generator", "service",
}

// PREFIX~N[.EXT] — 8.3 base chars, a tilde+ordinal, and an optional truncated extension.
var fragmentRe = regexp.MustCompile(`(?i)([a-z0-9_~!@#$%^&(){}'.\- ]{1,6})~[0-9]{1,2}(?:\.([a-z0-9]{1,3}))?`)

func stripExt(name string) string {
	if i := strings.LastIndex(name, "."); i > 0 {
		return name[:i]
	}
	return name
}

func expandExt(ext83 string) []string {
	if ext83 == "" {
		return []string{""}
	}
	var out []string
	seen := map[string]bool{}
	for _, e := range knownExtensions {
		if _, _, e83 := shortutil.Gen8dot3("x", e); strings.EqualFold(e83, ext83) && !seen[e] {
			seen[e] = true
			out = append(out, e)
		}
	}
	if len(out) == 0 { // unknown 8.3 extension: fall back to the literal 3 chars
		out = []string{strings.ToLower(ext83)}
	}
	return out
}

// generateBases returns candidate full base names for an 8.3 base prefix.
func generateBases(prefix string, words, suffixes, seps []string, compound bool) []string {
	p := strings.ToLower(prefix)
	up := strings.ToUpper(prefix)
	set := map[string]bool{p: true} // the prefix itself: a <6 base is complete, a 6 base may be
	if len(prefix) < 6 {
		return []string{p} // complete base — nothing to append
	}
	// 6-char (truncated) base: real completions from the wordlist ...
	for _, w := range words {
		if _, b83, _ := shortutil.Gen8dot3(w, ""); strings.EqualFold(b83, up) {
			set[strings.ToLower(w)] = true
		}
	}
	// ... and separator compounding.
	if compound {
		for _, sep := range seps {
			for _, suf := range suffixes {
				cand := p + sep + suf
				if _, b83, _ := shortutil.Gen8dot3(cand, ""); strings.EqualFold(b83, up) {
					set[cand] = true
				}
			}
		}
	}
	out := make([]string, 0, len(set))
	for b := range set {
		out = append(out, b)
	}
	sort.Strings(out)
	return out
}

func readLines(path string) ([]string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	var lines []string
	s := bufio.NewScanner(f)
	s.Buffer(make([]byte, 1024*1024), 1024*1024)
	for s.Scan() {
		if t := strings.TrimSpace(s.Text()); t != "" && !strings.HasPrefix(t, "#") {
			lines = append(lines, t)
		}
	}
	return lines, s.Err()
}

type frag struct{ prefix, ext string }

func scrapeFragments(text string, override string) []frag {
	var fs []frag
	for _, m := range fragmentRe.FindAllStringSubmatch(text, -1) {
		pre := strings.TrimRight(m[1], ". ")
		if pre == "" {
			continue
		}
		ext := m[2]
		if ext == "" {
			ext = override
		}
		fs = append(fs, frag{pre, ext})
	}
	return fs
}

func main() {
	urlList := flag.String("url", "", "comma-separated URL(s) to fetch and scrape real names/folders from (dynamic source; feeds both output and 6-char completion)")
	wordlist := flag.String("w", "", "wordlist of candidate base names/words for 6-char completions")
	suffixFile := flag.String("suffix", "", "suffix wordlist for separator compounding (default: built-in)")
	sepStr := flag.String("sep", "-,_,., ", "comma-separated separators for compounding (empty string always included)")
	extOverride := flag.String("ext", "", "8.3 extension to assume when a fragment has none (e.g. CON)")
	compound := flag.Bool("compound", false, "enable separator compounding (prefix+{-,_,.}+suffix; broad but noisy/low-precision — the real signal is -url + -w completion)")
	outPath := flag.String("o", "", "output file (default: stdout)")
	flag.Parse()

	var words []string
	if *wordlist != "" {
		w, err := readLines(*wordlist)
		if err != nil {
			fmt.Fprintln(os.Stderr, "wordlist:", err)
			os.Exit(1)
		}
		words = w
	}
	suffixes := defaultSuffixes
	if *suffixFile != "" {
		s, err := readLines(*suffixFile)
		if err != nil {
			fmt.Fprintln(os.Stderr, "suffix:", err)
			os.Exit(1)
		}
		suffixes = s
	}
	seps := append([]string{""}, strings.Split(*sepStr, ",")...)

	// Dynamic source: scrape real names from the target's own reachable content.
	siteNames := map[string]bool{}
	if *urlList != "" {
		for _, u := range strings.Split(*urlList, ",") {
			if u = strings.TrimSpace(u); u != "" {
				fetchNames(u, false, siteNames)
			}
		}
		for name := range siteNames {
			words = append(words, stripExt(name)) // base form completes 6-char fragments (ext re-added by expansion)
		}
	}

	// Collect fragments from args and from stdin (a piped shortscan run).
	var frags []frag
	for _, a := range flag.Args() {
		if fs := scrapeFragments(a, *extOverride); len(fs) > 0 {
			frags = append(frags, fs...)
		} else if a != "" { // a bare prefix like "WEB"
			frags = append(frags, frag{strings.TrimRight(a, ". "), *extOverride})
		}
	}
	if fi, err := os.Stdin.Stat(); err == nil && (fi.Mode()&os.ModeCharDevice) == 0 {
		s := bufio.NewScanner(os.Stdin)
		s.Buffer(make([]byte, 1024*1024), 1024*1024)
		for s.Scan() {
			frags = append(frags, scrapeFragments(s.Text(), *extOverride)...)
		}
	}
	if len(frags) == 0 && len(siteNames) == 0 {
		fmt.Fprintln(os.Stderr, "usage: shortgen [flags] FRAGMENT...   (or pipe shortscan output, or use -url)")
		fmt.Fprintln(os.Stderr, "example: shortgen WEB~1.CON APP_WE~1.DLL -w words.txt -o cands.txt")
		fmt.Fprintln(os.Stderr, "example: shortscan http://t/ | shortgen -url http://t/PRUEBA.html")
		os.Exit(2)
	}

	// Deduplicate fragments, then generate.
	seenFrag := map[string]bool{}
	out := map[string]bool{}
	for _, f := range frags {
		key := strings.ToUpper(f.prefix) + "|" + strings.ToUpper(f.ext)
		if seenFrag[key] {
			continue
		}
		seenFrag[key] = true
		exts := expandExt(strings.ToUpper(f.ext))
		for _, base := range generateBases(f.prefix, words, suffixes, seps, *compound) {
			for _, e := range exts {
				if e == "" {
					out[base] = true
				} else {
					out[base+"."+e] = true
				}
			}
		}
	}

	// Real names scraped from the site are candidates in their own right (referenced files
	// and folders worth (re)scanning), on top of the fragment-driven ones.
	for name := range siteNames {
		out[name] = true
	}

	names := make([]string, 0, len(out))
	for n := range out {
		names = append(names, n)
	}
	sort.Strings(names)

	w := os.Stdout
	if *outPath != "" {
		f, err := os.Create(*outPath)
		if err != nil {
			fmt.Fprintln(os.Stderr, "output:", err)
			os.Exit(1)
		}
		defer f.Close()
		w = f
	}
	bw := bufio.NewWriter(w)
	defer bw.Flush()
	for _, n := range names {
		fmt.Fprintln(bw, n)
	}
	fmt.Fprintf(os.Stderr, "shortgen: %d fragment(s) -> %d candidate names\n", len(seenFrag), len(names))
}
