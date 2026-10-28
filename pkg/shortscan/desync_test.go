package shortscan

import (
	"net"
	"testing"
	"time"
)

func TestTEFramedDetection(t *testing.T) {
	// 2nd response 200 => the leftover "GET /" formed => TE-framed => smuggle-able.
	if !teFramed([]string{"404 Not Found", "200 OK"}) {
		t.Error("a 2nd 200 must be detected as TE-framed")
	}
	// control shape: 2nd response is a method error (CL ate the 'G', 'ET' is invalid).
	if teFramed([]string{"404 Not Found", "405 Method Not Allowed"}) {
		t.Error("a 2nd non-200 (the pure-CL control) must NOT be TE-framed")
	}
	// single response => body consumed, no smuggle.
	if teFramed([]string{"404 Not Found"}) {
		t.Error("a single response must NOT be TE-framed")
	}
	if teFramed(nil) {
		t.Error("no responses must NOT be TE-framed")
	}
}

func TestTEFramedUsesCalibratedNon200Status(t *testing.T) {
	statuses := []string{"404 Not Found", "302 Found"}
	if !teFramed(statuses, "302 Found") {
		t.Fatal("a second response matching the calibrated redirect must prove TE framing")
	}
	if teFramed(statuses, "401 Unauthorized") {
		t.Fatal("a different second response must not match the calibration")
	}
	if teFramed([]string{"404 Not Found", "400 Bad Request"}, "302 Found") {
		t.Fatal("the pure-CL method error must not match the clean GET calibration")
	}
}

func TestTEDesyncProbeParsesResponses(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	// Mock a TE-framed back end: two responses on one connection (404 then 200).
	go func() {
		conn, e := ln.Accept()
		if e != nil {
			return
		}
		defer conn.Close()
		_ = conn.SetReadDeadline(time.Now().Add(5 * time.Second))
		buf := make([]byte, 4096)
		_, _ = conn.Read(buf)
		_, _ = conn.Write([]byte("HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n" +
			"HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"))
	}()
	block := "Host: 127.0.0.1\r\nContent-Length: 6\r\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\n\r\n"
	statuses, err := teDesyncProbe(ln.Addr().String(), "127.0.0.1", block)
	if err != nil {
		t.Fatal(err)
	}
	if len(statuses) != 2 || !teFramed(statuses) {
		t.Fatalf("expected two responses with a 2nd 200 (TE-framed), got %v", statuses)
	}
}

func TestDesyncVariantsIncludeBareLFHidden(t *testing.T) {
	// The variant table must carry at least one bare-LF-hidden (stronger) form,
	// and every hidden variant must actually embed a bare LF a CRLF parser folds.
	var nHidden int
	for _, v := range desyncVariants {
		block := v.build("h")
		if v.hidden {
			nHidden++
			// a bare LF is an "\n" not preceded by "\r"
			if !hasBareLF(block) {
				t.Errorf("hidden variant %q has no bare LF in its header block", v.label)
			}
		}
	}
	if nHidden == 0 {
		t.Error("expected at least one bare-LF-hidden desync variant")
	}
	// The control must be a clean CRLF block with no bare LF.
	if hasBareLF(desyncControlBlock("h")) {
		t.Error("control block must not contain a bare LF")
	}
}

func hasBareLF(s string) bool {
	for i := 0; i < len(s); i++ {
		if s[i] == '\n' && (i == 0 || s[i-1] != '\r') {
			return true
		}
	}
	return false
}
