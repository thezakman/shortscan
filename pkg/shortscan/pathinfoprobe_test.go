package shortscan

import (
	"net/http"
	"strings"
	"testing"
)

func TestHasPathInfoHandlerExt(t *testing.T) {
	yes := []string{"download.ashx", "Page.aspx", "svc.asmx", "wcf.svc", "A~1.ASHX"}
	no := []string{"file.txt", "img.jpg", "style.css", "web.config", "noext", "script.js"}
	for _, n := range yes {
		if !hasPathInfoHandlerExt(n) {
			t.Errorf("expected %q to be a PathInfo-capable handler ext", n)
		}
	}
	for _, n := range no {
		if hasPathInfoHandlerExt(n) {
			t.Errorf("expected %q NOT to be a PathInfo-capable handler ext", n)
		}
	}
}

// reader handler: reflects the PathInfo tail and leaks a physical path; a
// path-illegal char (| " < > *) makes MapPath/File.* throw -> 500.
func readerRoundTrip(base string) roundTripFunc {
	return func(req *http.Request) (*http.Response, error) {
		tail := strings.TrimPrefix(req.URL.Path, base)
		if tail == "" || tail == "/" {
			return responseFor(req, http.StatusOK, "READER-NOPI"), nil
		}
		tail = strings.TrimPrefix(tail, "/")
		if strings.ContainsAny(tail, `|"<>*`) {
			return responseFor(req, http.StatusInternalServerError, `<html>Server Error in '/'. C:\freshdefault\x</html>`), nil
		}
		return responseFor(req, http.StatusOK, `NOFILE:C:\freshdefault\`+tail), nil
	}
}

func TestClassifyPathInfoReaderIsHighCandidate(t *testing.T) {
	client := &http.Client{Transport: readerRoundTrip("/reader.aspx")}
	v, ok := classifyPathInfo(client, &httpStats{}, "http://iis.test/reader.aspx")
	if !ok {
		t.Fatal("expected reachable")
	}
	if !v.accepts || !v.mapsFile || !v.reflects || !v.physLeak {
		t.Fatalf("reader should map+reflect+leak: %+v", v)
	}
	if v.confidence != "high" {
		t.Fatalf("reader should be high confidence, got %q", v.confidence)
	}
}

// noop handler: constant output, ignores PathInfo entirely.
func TestClassifyPathInfoNoopIsNone(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusOK, "STATIC-CONSTANT-OUTPUT"), nil
	})}
	v, ok := classifyPathInfo(client, &httpStats{}, "http://iis.test/noop.aspx")
	if !ok || !v.accepts {
		t.Fatalf("noop should be reachable and accept PathInfo: ok=%v %+v", ok, v)
	}
	if v.mapsFile || v.reflects {
		t.Fatalf("noop must not signal file-read or reflection: %+v", v)
	}
	if v.confidence != "none" {
		t.Fatalf("noop should be confidence none, got %q", v.confidence)
	}
}

// static file: base 200 but a PathInfo tail 404s -> not a PathInfo target.
func TestClassifyPathInfoStaticNotATarget(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.URL.Path == "/plain.txt" {
			return responseFor(req, http.StatusOK, "just a static file"), nil
		}
		return responseFor(req, http.StatusNotFound, "404"), nil
	})}
	v, ok := classifyPathInfo(client, &httpStats{}, "http://iis.test/plain.txt")
	if !ok {
		t.Fatal("expected reachable")
	}
	if v.accepts {
		t.Fatalf("static file should NOT accept PathInfo: %+v", v)
	}
	if v.confidence != "none" {
		t.Fatalf("static should be confidence none, got %q", v.confidence)
	}
}

// CONTROL: a handler that 5xx's on ANY PathInfo (broken, not MapPath) must NOT be
// flagged as a file-read candidate — the benign-not-5xx guard is what prevents the
// reqfilter-style false positive.
func TestClassifyPathInfoAll5xxIsNotFlagged(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.URL.Path == "/broken.aspx" {
			return responseFor(req, http.StatusOK, "OK"), nil
		}
		return responseFor(req, http.StatusInternalServerError, "boom"), nil
	})}
	v, ok := classifyPathInfo(client, &httpStats{}, "http://iis.test/broken.aspx")
	if !ok {
		t.Fatal("expected reachable")
	}
	if v.mapsFile {
		t.Fatalf("a handler that 5xx's on every PathInfo must not be a file-read candidate: %+v", v)
	}
	if v.confidence != "none" {
		t.Fatalf("broken-500 handler should be none, got %q", v.confidence)
	}
}

// finding 5: PathInfo tail must go before a query string, not into it.
func TestAppendPathInfoPreservesQuery(t *testing.T) {
	cases := map[string]string{
		"http://h/x.ashx":           "http://h/x.ashx/tail",
		"http://h/x.ashx/":          "http://h/x.ashx/tail",
		"http://h/x.ashx?id=1":      "http://h/x.ashx/tail?id=1",
		"http://h/x.ashx/?id=1&a=b": "http://h/x.ashx/tail?id=1&a=b",
	}
	for in, want := range cases {
		if got := appendPathInfo(in, "tail"); got != want {
			t.Errorf("appendPathInfo(%q) = %q, want %q", in, got, want)
		}
	}
}

// finding 6: a carrier that is itself 404 is not a live handler and must not be
// probed/classified (even if a path-illegal tail happens to 5xx).
func TestClassifyPathInfoBase404IsNotAHandler(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if strings.ContainsAny(req.URL.Path, `|"`) {
			return responseFor(req, http.StatusInternalServerError, "boom"), nil
		}
		return responseFor(req, http.StatusNotFound, "nope"), nil
	})}
	v, ok := classifyPathInfo(client, &httpStats{}, "http://iis.test/ghost.aspx")
	if !ok {
		t.Fatal("reachable")
	}
	if v.accepts || v.mapsFile || v.confidence != "none" {
		t.Fatalf("a base-404 endpoint must not be probed/flagged: %+v", v)
	}
}

// finding 7: a benign body that merely contains a C:\ string must not set physLeak
// (which is corroboration for MapPath) and must not promote confidence.
func TestClassifyPathInfoBenignDrivePathDoesNotPromote(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		return responseFor(req, http.StatusOK, `sample path C:\Users\docs, constant output`), nil
	})}
	v, _ := classifyPathInfo(client, &httpStats{}, "http://iis.test/docs.aspx")
	if v.physLeak {
		t.Fatalf("physLeak must not come from a benign body: %+v", v)
	}
	if v.mapsFile || v.confidence == "high" {
		t.Fatalf("a constant page with a C:\\ string must not be a candidate: %+v", v)
	}
}

// finding 4: with a mix of illegal-char statuses, the displayed illegalStatus must
// reflect the 5xx probe (the mapping signal), not whichever ran last.
func TestClassifyPathInfoIllegalStatusPrefers5xx(t *testing.T) {
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		p := req.URL.Path
		if strings.Contains(p, "|") {
			return responseFor(req, http.StatusInternalServerError, `err C:\x`), nil
		}
		if strings.Contains(p, `"`) {
			return responseFor(req, http.StatusNotFound, "nf"), nil
		}
		return responseFor(req, http.StatusOK, "ok"), nil
	})}
	v, _ := classifyPathInfo(client, &httpStats{}, "http://iis.test/mix.aspx")
	if !v.mapsFile {
		t.Fatalf("one 5xx illegal probe should set mapsFile: %+v", v)
	}
	if v.illegalStatus/100 != 5 {
		t.Fatalf("illegalStatus should reflect the 5xx probe, got %d", v.illegalStatus)
	}
}

func TestLooksLikeWebConfig(t *testing.T) {
	if !looksLikeWebConfig([]byte(`<?xml version="1.0"?><configuration><system.web/></configuration>`)) {
		t.Error("should recognise a web.config")
	}
	if looksLikeWebConfig([]byte(`<html><body>ordinary page</body></html>`)) {
		t.Error("should not recognise arbitrary HTML as web.config")
	}
}

// confirmingReaderRoundTrip: a handler that reads PathInfo AND whose /web.config is
// RF-blocked on the direct path but readable via PathInfo.
func confirmingReaderRoundTrip() roundTripFunc {
	webcfg := `<?xml version="1.0"?><configuration><appSettings><add key="k" value="TOPSECRET"/></appSettings><system.web/></configuration>`
	return func(req *http.Request) (*http.Response, error) {
		p := req.URL.Path
		switch {
		case p == "/web.config": // direct -> RequestFiltering block
			return responseFor(req, http.StatusNotFound, `<title>IIS 10.0 - 404.8</title> RequestFilteringModule`), nil
		case strings.HasSuffix(p, "/web.config"): // via PathInfo -> served by the handler
			return responseFor(req, http.StatusOK, webcfg), nil
		case strings.ContainsAny(p, `|"`):
			return responseFor(req, http.StatusInternalServerError, `err C:\inetpub\wwwroot\x`), nil
		default:
			return responseFor(req, http.StatusOK, "READ-NOPI"), nil
		}
	}
}

func TestClassifyPathInfoConfirmsFileRead(t *testing.T) {
	client := &http.Client{Transport: confirmingReaderRoundTrip()}
	v, ok := classifyPathInfo(client, &httpStats{}, "http://iis.test/read.aspx")
	if !ok || !v.confirmed || v.confidence != "confirmed" {
		t.Fatalf("expected a confirmed file read: %+v", v)
	}
	if !strings.Contains(v.confirmEvid, "web.config") {
		t.Fatalf("evidence should cite web.config: %q", v.confirmEvid)
	}
	if strings.Contains(v.confirmEvid, "TOPSECRET") {
		t.Fatalf("evidence must be a signature, NOT leak the secret value: %q", v.confirmEvid)
	}
}

// A world-readable web.config (served on the direct path too) is not an RF bypass.
func TestConfirmPathInfoReadNotBypassWhenDirectServes(t *testing.T) {
	webcfg := `<?xml version="1.0"?><configuration><system.web/></configuration>`
	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if strings.Contains(req.URL.Path, "web.config") {
			return responseFor(req, http.StatusOK, webcfg), nil // served everywhere
		}
		return responseFor(req, http.StatusOK, "x"), nil
	})}
	if ok, _ := confirmPathInfoRead(client, &httpStats{}, "http://iis.test/read.aspx"); ok {
		t.Fatal("must not confirm an RF bypass when /web.config is served directly")
	}
}
