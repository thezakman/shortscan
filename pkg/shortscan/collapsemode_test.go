package shortscan

import (
	"net/http"
	"strings"
	"testing"
)

func TestParsePhysicalPath(t *testing.T) {
	body := []byte(`<tr><th>Caminho Físico</th><td>&nbsp;&nbsp;&nbsp;C:\inetpub\wwwroot\web.config</td></tr>`)
	if got := parsePhysicalPath(body); got != `C:\inetpub\wwwroot\web.config` {
		t.Fatalf("parsePhysicalPath = %q, want the wwwroot path", got)
	}
	if got := parsePhysicalPath([]byte("<html>no path here</html>")); got != "" {
		t.Fatalf("want empty when no path present, got %q", got)
	}
}

// collapseClient mocks IIS's detailed-error physical path for the ext-split probe
// /(S(1))/aq<rnd>/(S(1))wx<rnd>: merged=true simulates aggressive removal (a+b
// reunited, no token) and merged=false simulates the conservative patch (embedded
// token survives).
func collapseClient(merged bool) *http.Client {
	return &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		parts := strings.Split(req.URL.EscapedPath(), "/") // ["","(S(1))","aqX","(S(1))wxX"]
		var a, b string
		if len(parts) >= 4 {
			a = parts[2]
			b = strings.TrimPrefix(parts[3], "(S(1))")
		}
		var phys string
		if merged {
			phys = `C:\inetpub\wwwroot\` + a + b
		} else {
			phys = `C:\inetpub\wwwroot\` + a + `\(S(1))` + b
		}
		return responseFor(req, http.StatusNotFound, `<tr><th>Caminho Físico</th><td>`+phys+`</td></tr>`), nil
	})}
}

func TestClassifyCollapseModeAggressive(t *testing.T) {
	mode, phys := classifyCollapseMode(collapseClient(true), &httpStats{}, "http://lab.test")
	if !strings.HasPrefix(mode, "AGGRESSIVE") {
		t.Fatalf("merged physical path must classify AGGRESSIVE, got %q (phys %q)", mode, phys)
	}
	if !strings.Contains(mode, "CVE-2023-36899") {
		t.Fatalf("aggressive verdict should name the CVE, got %q", mode)
	}
}

func TestClassifyCollapseModeConservative(t *testing.T) {
	mode, phys := classifyCollapseMode(collapseClient(false), &httpStats{}, "http://lab.test")
	if !strings.HasPrefix(mode, "conservative") {
		t.Fatalf("surviving embedded token must classify conservative/patched, got %q (phys %q)", mode, phys)
	}
}

func TestClassifyCollapseModeNoCookieless(t *testing.T) {
	// A host that does NO cookieless path removal (non-ASP.NET / cookieless off)
	// leaves BOTH tokens in the physical path — must be reported as n/a, not as
	// "patched" (which would imply ASP.NET cookieless is present).
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		parts := strings.Split(req.URL.EscapedPath(), "/")
		var a, b string
		if len(parts) >= 4 {
			a = parts[2]
			b = strings.TrimPrefix(parts[3], "(S(1))")
		}
		phys := `C:\inetpub\wwwroot\(S(1))\` + a + `\(S(1))` + b // nothing removed
		return responseFor(req, http.StatusNotFound, `<tr><th>Caminho Físico</th><td>`+phys+`</td></tr>`), nil
	})}
	mode, phys := classifyCollapseMode(client, &httpStats{}, "http://lab.test")
	if !strings.HasPrefix(mode, "n/a") {
		t.Fatalf("two surviving tokens must classify n/a (no cookieless removal), got %q (phys %q)", mode, phys)
	}
}

func TestClassifyCollapseModeNoDetailedErrors(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusNotFound, "<html>generic 404, no physical path</html>"), nil
	})}
	mode, phys := classifyCollapseMode(client, &httpStats{}, "http://lab.test")
	if mode != "" || phys != "" {
		t.Fatalf("without a disclosed physical path the detector must stay silent, got %q / %q", mode, phys)
	}
}
