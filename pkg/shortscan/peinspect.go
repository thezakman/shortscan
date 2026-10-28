package shortscan

import (
	"regexp"
	"strconv"
	"strings"

	"github.com/thezakman/shortscan/pkg/dotnetmeta"
)

// peinspect.go turns a disclosed .NET assembly into MORE than shortscan's 8.3 output.
// A compiled ASP.NET assembly (App_Web_*.dll, App_Code.*.dll) embeds, in its PE debug
// directory and CLI metadata heaps, the FULL PDB build path, every identifier name
// (#Strings) and every string literal (#US: a page's static HTML markup + hard-coded
// secrets) — long names the tilde oracle cannot reach. The heavy lifting lives in the
// dependency-free pkg/dotnetmeta; here we render a concise inline summary and point at
// `shortloot` for the complete dump.

type assemblyInfo struct {
	IsPE        bool     `json:"is_pe"`
	PDBPath     string   `json:"pdb_path,omitempty"`
	Namespaces  []string `json:"namespaces,omitempty"`
	Secrets     []string `json:"secrets,omitempty"` // literals that look like secrets/URLs
	SourceLinks []string `json:"source_links,omitempty"`
	NameCount   int      `json:"name_count,omitempty"`
	LitCount    int      `json:"literal_count,omitempty"`
}

// a namespace-ish identifier: dotted, capitalised segments, not a framework namespace.
var reNamespace = regexp.MustCompile(`^[A-Z][A-Za-z0-9]*(\.[A-Z][A-Za-z0-9]*){1,6}$`)

// literals worth surfacing inline: connection strings, credentials, keys, repo URLs.
var reSecretish = regexp.MustCompile(`(?i)(server=|data source=|password|pwd=|user id=|connectionstring|secret|api[_-]?key|bearer |authorization|machinekey|https?://[^ ]*(github|gitlab|azure|/_git/))`)

// reRealAssignment requires an actual "key=value" pair before a reSecretish
// keyword hit is trusted: a '=' not immediately preceded by !/</>/= (so it
// isn't part of a comparison operator: !=, ==, <=, >=) and not immediately
// followed by =/%/{ (so it isn't a template placeholder like "={0}" or "=%s").
// A connection string ("Server=x;Pwd=y") or an XML attribute ("machineKey
// validationKey=\"...\"") always has this shape; noise never does.
//
// reBearerToken separately allows a "Bearer <token>" literal through even
// without an '=' — an Authorization header value is a real secret shape too.
//
// Verified against every "secret literal" surfaced across two live disclosures
// (EntityFramework.dll, iTextSharp.dll, Microsoft.ReportViewer.Common.dll,
// System.Web.Mvc.dll, System.Web.Helpers.dll on a real /bin dump): 21 hits with
// NO '=' were ALL noise — bare property/field names ("password", "Authorization",
// "ConnectionString", "hashedPassword"), dotted resource-message keys
// ("bad.user.password", "pdfreader.not.opened.with.owner.password"), natural-
// language error-message text ("No password finder specified, but a password is
// required"), and UI description strings ("text-box single-line password").
// Zero of them were this deployment's own data. The one hit that DID carry a real
// assignment ("Data Source=.\SQLEXPRESS; Integrated Security=True;...") is the
// only one worth a human's second look, even though it's EF's own stock
// LocalDB-convention default rather than an app secret — a narrower, name-specific
// exclusion for that exact vendor string would be brittle and isn't worth adding.
var reRealAssignment = regexp.MustCompile(`[^!<>=]=[^=%{]`)
var reBearerToken = regexp.MustCompile(`(?i)bearer\s+[A-Za-z0-9._-]{16,}`)

// looksLikeSecretValue rejects a reSecretish match that is just a property/field
// name, resource-message key, or natural-language error text mentioning a
// secret-ish word, rather than a real credential value.
func looksLikeSecretValue(l string) bool {
	return reRealAssignment.MatchString(l) || reBearerToken.MatchString(l)
}

var frameworkNS = []string{"System", "Microsoft.", "Newtonsoft.", "mscorlib", "Windows."}

func inspectAssemblyBytes(raw []byte) *assemblyInfo {
	asm, err := dotnetmeta.Inspect(raw)
	if err != nil || asm == nil {
		return nil
	}
	info := &assemblyInfo{IsPE: asm.IsPE, PDBPath: asm.PDBPath, NameCount: len(asm.Names), LitCount: len(asm.Literals)}

	nsSeen := map[string]struct{}{}
	for _, n := range asm.Names {
		if !reNamespace.MatchString(n) || isFrameworkNS(n) {
			continue
		}
		if _, ok := nsSeen[n]; ok {
			continue
		}
		nsSeen[n] = struct{}{}
		info.Namespaces = append(info.Namespaces, n)
		if len(info.Namespaces) >= 12 {
			break
		}
	}
	for _, l := range asm.Literals {
		if len(l) < 4 || len(l) > 200 || !reSecretish.MatchString(l) {
			continue
		}
		if !looksLikeSecretValue(l) {
			continue
		}
		if strings.Contains(strings.ToLower(l), "/_git/") || regexpSourceLink.MatchString(l) {
			info.SourceLinks = append(info.SourceLinks, l)
		} else {
			info.Secrets = append(info.Secrets, l)
		}
		if len(info.Secrets)+len(info.SourceLinks) >= 12 {
			break
		}
	}
	return info
}

var regexpSourceLink = regexp.MustCompile(`(?i)https?://[^ ]*(github|gitlab|bitbucket|dev\.azure|/_git/)`)

func isFrameworkNS(s string) bool {
	for _, p := range frameworkNS {
		if s == p || strings.HasPrefix(s, p) {
			return true
		}
	}
	return false
}

// summary renders the recovered metadata as short lines (nil-safe).
func (a *assemblyInfo) summary() []string {
	if a == nil {
		return nil
	}
	var out []string
	if a.PDBPath != "" {
		out = append(out, "PDB/build path: "+a.PDBPath)
	}
	if len(a.Namespaces) > 0 {
		out = append(out, "namespaces/types: "+joinComma(a.Namespaces))
	}
	for _, s := range a.Secrets {
		out = append(out, "secret literal: "+s)
	}
	for _, l := range a.SourceLinks {
		out = append(out, "SourceLink: "+l)
	}
	if a.NameCount > 0 || a.LitCount > 0 {
		out = append(out, "(+"+strconv.Itoa(a.NameCount)+" names, "+strconv.Itoa(a.LitCount)+" literals — run `shortloot --all <file>` for the full source dump)")
	}
	return out
}

func joinComma(ss []string) string {
	return strings.Join(ss, ", ")
}
