package shortscan

import (
	"strings"
	"testing"
)

func TestH2CasesHaveControlAndDangerous(t *testing.T) {
	cases := h2Cases("h.test")
	var nControl, nDanger, nSpacePath int
	for _, c := range cases {
		if c.control {
			nControl++
			// the control must be a valid request (root path, no illegal chars)
			for _, f := range c.fields {
				if f.Name == ":path" && f.Value != "/" {
					t.Errorf("control case has a non-root :path %q", f.Value)
				}
			}
		}
		if c.dangerous {
			nDanger++
		}
		for _, f := range c.fields {
			if f.Name == ":path" && strings.ContainsAny(f.Value, " \t") {
				nSpacePath++
			}
		}
	}
	if nControl != 1 {
		t.Errorf("expected exactly one control case, got %d", nControl)
	}
	if nDanger < 3 {
		t.Errorf("expected several dangerous (RFC-illegal) cases, got %d", nDanger)
	}
	if nSpacePath == 0 {
		t.Error("expected at least one :path with a space/tab (the h1-illegal request-line-split probe)")
	}
}

func TestH2HostPortDefaultsTo443(t *testing.T) {
	if got := h2HostPort("host.test"); got != "host.test:443" {
		t.Errorf("expected host.test:443, got %s", got)
	}
	if got := h2HostPort("host.test:8443"); got != "host.test:8443" {
		t.Errorf("explicit port must be preserved, got %s", got)
	}
}

// A bracketed IPv6 literal with no port ("[::1]", exactly what url.URL.Host
// gives for https://[::1]/) contains colons from the address itself — a bare
// ":" check would wrongly treat that as "already has a port" and hand the
// dialer an unbracketed, portless host. Must still default to :443 and stay
// bracketed.
func TestH2HostPortHandlesIPv6(t *testing.T) {
	if got := h2HostPort("[::1]"); got != "[::1]:443" {
		t.Errorf("expected [::1]:443, got %s", got)
	}
	if got := h2HostPort("[2001:db8::1]"); got != "[2001:db8::1]:443" {
		t.Errorf("expected [2001:db8::1]:443, got %s", got)
	}
	if got := h2HostPort("[::1]:8443"); got != "[::1]:8443" {
		t.Errorf("explicit port on an IPv6 literal must be preserved, got %s", got)
	}
}

func TestH2StatusDifferentialIsNeverConfirmedSplit(t *testing.T) {
	verdict, _ := classifyH2PathDifferential("404", "400", false, false, "detail")
	if verdict != "backend-error-differential" {
		t.Fatalf("400 status-only result = %q, want conservative differential", verdict)
	}
	verdict, _ = classifyH2PathDifferential("404", "500", false, false, "detail")
	if verdict != "status-differential" {
		t.Fatalf("generic status-only result = %q, want conservative differential", verdict)
	}
	verdict, _ = classifyH2PathDifferential("404", "400", false, true, "detail")
	if verdict != "front-end-rejected" {
		t.Fatalf("front-end rejection = %q", verdict)
	}
}
