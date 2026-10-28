package shortscan

import (
	"bytes"
	"net/http"
	"strings"
	"testing"
)

func fingerprintClient(copyOnConfig bool) *http.Client {
	return &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		if req.Method == "PROPFIND" {
			res := responseFor(req, http.StatusMethodNotAllowed, "")
			allow := "GET, HEAD, OPTIONS, TRACE, LOCK, UNLOCK"
			if copyOnConfig && strings.EqualFold(req.URL.Path, "/web.config") {
				allow += ", COPY"
			}
			res.Header.Set("Allow", allow)
			return res, nil
		}
		if req.Method == http.MethodOptions {
			res := responseFor(req, http.StatusOK, "")
			res.Header.Set("DAV", "1,2,3")
			res.Header.Set("Allow", "GET, HEAD, OPTIONS, PROPFIND, COPY, LOCK")
			return res, nil
		}
		body := "IIS 10.0 - 404.0 - Not Found RequestFilteringModule"
		res := responseFor(req, http.StatusNotFound, body)
		res.Header.Set("Server", "Microsoft-IIS/10.0")
		if strings.Contains(strings.ToLower(req.URL.Path), "/bin/") || req.URL.Path == "/web.config" {
			res.Body.Close()
			res = responseFor(req, http.StatusNotFound, "IIS 10.0 - 404.8 - Not Found RequestFilteringModule")
			res.Header.Set("Server", "Microsoft-IIS/10.0")
		}
		return res, nil
	})}
}

func TestParseIISDetail(t *testing.T) {
	version, substatus, module := parseIISDetail([]byte("IIS 10.0 - 404.8 - Not Found RequestFilteringModule"))
	if version != "10.0" || substatus != "404.8" || module != "RequestFilteringModule" {
		t.Fatalf("unexpected IIS detail: version=%q substatus=%q module=%q", version, substatus, module)
	}
}

func TestFingerprintDoesNotPromoteUnpairedAllowHeader(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousDone, previousBaselines := fingerprintDone, allowCopyBaselines
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		fingerprintDone, allowCopyBaselines = previousDone, previousBaselines
	}()
	args = arguments{Output: "human", Retries: 0}
	fingerprintDone = make(map[string]bool)
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	var output bytes.Buffer
	outputWriter = &output

	runFingerprint("http://example.test/", fingerprintClient(false), &httpStats{}, true, "Microsoft-IIS/10.0", false)
	if strings.Contains(output.String(), "allow-copy oracle available") {
		t.Fatalf("unpaired 405/Allow was promoted: %q", output.String())
	}
}

func TestFingerprintRequiresFullAllowCopyDifferential(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousDone, previousBaselines := fingerprintDone, allowCopyBaselines
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		fingerprintDone, allowCopyBaselines = previousDone, previousBaselines
	}()
	args = arguments{Output: "human", Retries: 0}
	fingerprintDone = make(map[string]bool)
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	var output bytes.Buffer
	outputWriter = &output

	runFingerprint("http://example.test/", fingerprintClient(true), &httpStats{}, true, "Microsoft-IIS/10.0", false)
	if !strings.Contains(output.String(), "allow-copy oracle available") {
		t.Fatalf("paired Allow/COPY differential was not surfaced: %q", output.String())
	}
}

func TestFingerprintNonIISBannerStaysAmbiguous(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousDone, previousBaselines := fingerprintDone, allowCopyBaselines
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		fingerprintDone, allowCopyBaselines = previousDone, previousBaselines
	}()
	args = arguments{Output: "human", Retries: 0}
	fingerprintDone = make(map[string]bool)
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	var output bytes.Buffer
	outputWriter = &output

	client := &http.Client{Transport: roundTripFunc(func(req *http.Request) (*http.Response, error) {
		res := responseFor(req, http.StatusNotFound, "generic miss")
		res.Header.Set("Server", "nginx")
		return res, nil
	})}
	runFingerprint("http://example.test/", client, &httpStats{}, true, "nginx [!]", true)
	got := output.String()
	if (!strings.Contains(got, "Cross-stack candidate") || !strings.Contains(got, "file access not confirmed")) || strings.Contains(got, "STRONG") || strings.Contains(got, "likely discloses") {
		t.Fatalf("non-IIS banner verdict was overclaimed: %q", got)
	}
}

func TestFingerprintUpgradesTildeResultDuringRecursion(t *testing.T) {
	previousArgs, previousWriter := args, outputWriter
	previousDone, previousBaselines := fingerprintDone, allowCopyBaselines
	defer func() {
		args, outputWriter = previousArgs, previousWriter
		fingerprintDone, allowCopyBaselines = previousDone, previousBaselines
	}()
	args = arguments{Output: "human", Retries: 0}
	fingerprintDone = make(map[string]bool)
	allowCopyBaselines = make(map[string]allowCopyBaseline)
	var output bytes.Buffer
	outputWriter = &output

	client := fingerprintClient(false)
	runFingerprint("http://example.test/first/", client, &httpStats{}, false, "Microsoft-IIS/10.0", false)
	firstLen := output.Len()
	runFingerprint("http://example.test/second/", client, &httpStats{}, true, "Microsoft-IIS/10.0", false)
	upgrade := output.String()[firstLen:]
	if !strings.Contains(upgrade, "8.3:yes") {
		t.Fatalf("later vulnerable directory did not upgrade fingerprint: %q", upgrade)
	}
}
