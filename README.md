# 🌀 Shortscan

An IIS short filename enumeration and canonicalization research tool. **v1.81.0**
adds guarded cross-stack reads through directory `$INDEX_ALLOCATION` namespaces
after confirming an Express route-auth bypass on Windows. v1.80.1 added
high-value detection for IIS WebDAV `properties.dav` databases recovered through
guarded cross-stack 8.3 retrieval. v1.80.0 added a validated
IIS/System.Web research bundle for request-body limits, multipart
cache keys and FastCGI header namespaces. v1.79.0 turns conventional
request-filtered ASP.NET/NuGet manifests into quarantined stem
evidence for actively verified, readable sibling names. v1.78.0 extended the
cross-stack retrieval chain to known NTFS named streams after confirming
that Node `serve-static` 2.2.1 serves both an 8.3 alias and its named ADS, and that
ASP.NET Core 10.0.12 default StaticFileMiddleware serves MIME-mapped aliases, from
the same Windows NTFS root where IIS blocks them. v1.76.0 added a fully enumerable
header-signature oracle for reverse proxies/WAFs that flatten the IIS status
differential while preserving categorical origin headers. v1.45.0 makes
method-magic self-validating per extension: a `405` "this exists" only counts when it differs
from a same-extension baseline, so 405-for-everything servers stop producing recovered names
that don't exist — while requestFiltering-hidden files are still recovered wherever the `405`
signal is genuinely real. v1.44 added the extension-dimension catch-all guard. v1.43 killed
three false-positive sources against catch-all / soft-404 front ends (a `#` in an 8.3 alias
fetching the directory root, unguarded `--mutate-ext` hits, and serve-everything enumeration
explosions). v1.42 made `--maxtime` default to `0` (no limit) so a recursive `-r` scan is
never silently truncated.

## What's new in 1.81.0

- **Express route-auth bypass on Windows.** With authentication mounted
  on `/private` before `express.static(root)`, the canonical JSON/DLL requests
  returned 401 while both `private::$INDEX_ALLOCATION/<file>` and
  `private:$I30:$INDEX_ALLOCATION/<file>` returned the exact protected bytes.
  Raw and percent-encoded forms reproduced; missing-directory and missing-child
  controls stayed 404.
- Confirmed on Express 5.2.1 (`serve-static` 2.2.1 / `send` 1.2.1) and Express
  4.21.2 (`serve-static` 1.16.2 / `send` 0.19.0), Node.js 22.23.2, Windows NTFS.
  Go's standard `http.FileServer` was a negative cross-language control.
- **`--auto`/`--full` integration.** When a sensitive long name has been
  recovered and a non-IIS `--retrieve-base` is available, Shortscan now tries
  the two directory-index namespace spellings after the guarded 8.3 read. Every
  read requires a random same-extension child control to fail and reports only
  proven bytes as `[INDEX-READ/CRITICAL]`.
- `serve-index` 1.9.1 additionally turned the namespace into a full-LFN listing
  and child-read primitive behind a canonical directory deny.

## What's new in 1.80.1

- **WebDAV property-database retrieval.** A controlled shared-NTFS lab showed
  that IIS's `webdav_simple_prop` provider creates a Hidden+System
  `properties.dav`, while Node `serve-static` 2.2.1 returns the exact file through
  `PROPER~1.DAV`. A case-insensitive canonical-name deny returned 404 for
  `properties.dav`; the alias still returned 200 and the byte-identical database,
  including a synthetic secret marker and internal URL. A nonexistent alias stayed
  404.
- `--auto`/`--full` now classify a resolved `properties.dav` as high-value and use
  the existing `--retrieve-base` alias-plus-negative-control path to save it.
  UTF-16LE WebDAV property stores are identified explicitly instead of appearing
  as generic binary data.
- This is a cross-stack composition, not a default-IIS-only vulnerability. It
  requires WebDAV custom properties and another Windows static tier sharing the
  NTFS content root.

## What's new in 1.80

- Documents how chunked request bodies bypass IIS
  `maxAllowedContentLength`, including a same-payload WebDAV write at the default
  30,000,000-byte limit.
- Documents how ASP.NET `maxRequestLength` can be bypassed inside IIS's
  49,152-byte pre-read window when the request is chunked.
- Documents how `VaryByParam="*"` omits `Request.Files` from the System.Web
  OutputCache key whenever a multipart POST also has a normal form field.
- Documents how `CustomErrorModule` File mode reads a custom error body
  outside the file's URL-scoped authentication policy; direct anonymous access
  is 401 while an anonymous 404 returns the protected bytes.
- Also retains a regression/composition test for IIS `scanHeaders` and
  FastCGI header namespaces. The behavior is real, but its root class has public
  IIS/CGI prior art and is not counted as a new vulnerability.
- These are laboratory research probes, not automatic reconnaissance. `--auto`
  intentionally does not send state-changing uploads, oversized bodies, or
  application-significant authentication headers.

## What's new in 1.79

- **ASP.NET/NuGet manifest profile.** `--auto`/`--full` now recognize canonical
  project-root names that IIS normally request-filters: `AjaxControlToolkit.config`,
  `AppSettings.config`, `packages.config`, `web.config`, and `Global.asax`. This
  fixes the ambiguous `PACKAG~1.CON` guess: the conventional NuGet file is
  `packages.config`, not `package.config`.
- **Blocked manifest to readable sibling.** An inferred manifest stem is kept in a
  quarantined per-scan evidence store. It may generate only a bounded set of
  readable sibling candidates, such as `AppSettings.Production.txt` and
  `AppSettings-backup.txt`; every candidate must independently pass the selected
  HTTP oracle before it is reported. The blocked manifest itself remains marked
  `candidate, not confirmed`, with no invented ordinal.
- **Controlled content proof.** When a manifest-derived sibling is confirmed,
  automatic modes issue an exact GET and a random same-extension negative control.
  Non-empty bytes are reported as `[MANIFEST-SIBLING-READ]` and saved under
  `--loot-dir`; soft-404/serve-everything responses are rejected. Secret/config
  markers raise the result to `high`.
- Controlled IIS 10 validation recovered and saved `AppSettings-backup.txt` from
  an otherwise unresolved `APPSET~3.TXT`, while the same scan retained honest
  inference labels for `.config`/`.asax`. This improves enumeration and turns a
  publicly served backup sibling into a data-read proof; it is not a bypass that
  makes default IIS serve protected `.config` files.

## What's new in 1.78

- **Guarded cross-stack retrieval is now part of `--auto`/`--full`.** Every confirmed 8.3 alias is offered
  to the guarded retrieval chain. Single-stack IIS is skipped; a mixed-stack
  origin or an explicit `--retrieve-base` is tested with a random same-shape
  negative alias before any bytes are reported or saved.
- When the operator did not provide `--retrieve-stream`, automatic mode also
  probes the single well-known `Zone.Identifier` (Mark-of-the-Web) stream. This
  is a bounded known-name check, not ADS enumeration, and uses a negative alias
  carrying the identical `:Zone.Identifier:$DATA` suffix.
- Explicit streams still win: `--auto --retrieve-stream NAME` keeps only the
  operator-supplied stream list and now parses without requiring a redundant
  `--retrieve` flag.

## What's new in 1.77

- **Node/Express cross-stack retrieval is now lab-confirmed.** On Windows ARM64,
  `serve-static` 2.2.1 served `CONFID~1.TXT` with the exact bytes of
  `ConfidentialReportNode.txt`, while IIS 10 over the same directory returned 404.0.
  A fake same-shape alias returned 404. The end-to-end `--retrieve-base` run enumerated
  the alias through IIS and saved the 33-byte canary through the Node tier; the saved
  SHA-256 matched the source file.
- **Known named-ADS retrieval.** Repeat `--retrieve-stream NAME` with `--retrieve` to
  test a known NTFS alternate data stream through the selected retrieval tier, for
  example `--retrieve-stream Zone.Identifier`. Shortscan requests
  `SHORT~1.EXT:NAME:$DATA`, mirrors that exact suffix on a random same-shape negative
  alias, caps/sanitises loot, and saves each proven stream separately. It never guesses
  or enumerates unknown stream names.
- The lab confirmed both `ConfidentialReportNode.txt:hidden.txt` and
  `CONFID~1.TXT:hidden.txt` through `serve-static` 2.2.1, while IIS blocked the ADS URL.
  This is a mixed-stack deployment condition, not a claim that default IIS alone serves
  the data; nginx and Java remain untested, while Kestrel is covered separately below.
- **Same-vendor Kestrel control.** ASP.NET Core 10.0.12 with default
  `ServeUnknownFileTypes=false` resolved `CONFID~1.TXT` to the LFN and served its
  bytes. In an extension matrix, `QuarterlyPayrollExport2026.xlsx` was retrievable
  as `QUARTE~1.XLS`, while a fake alias and unmapped `.CON/.JSO/.PEM/.BAK/.ASP`
  aliases remained 404. Kestrel blocked named/default ADS even when unknown file
  types were enabled.
- With the non-default `ServeUnknownFileTypes=true`, the same controlled run
  retrieved 7/7 aliases including `.config`, `.json`, `.pem`, `.bak` and `.aspx`
  source canaries. Microsoft documents this toggle as a security risk; Shortscan
  reports what the selected tier actually serves rather than assuming it is set.

## What's new in 1.76

- **Header-signature ShortName enumeration.** Under `--auto`/`--full`, after all
  status oracles fail, Shortscan now calibrates categorical response metadata such as
  `Content-Type`, `Allow`, `DAV`, authentication and ASP.NET headers. It requires four
  agreeing same-shape negative controls, rejects a `~0` catch-all and repeats every
  positive tilde before trusting the signal. `Content-Length` and `Location` are excluded
  because IIS error pages can echo the requested path.
- Unlike the existing PROPFIND body fallback, the new oracle feeds character discovery
  and recursive ShortName enumeration. In the IIS 10 lab, a reverse proxy forced every
  response to `404` while preserving origin headers: the ordinary scan returned
  `Vulnerable: No`; v1.76 recovered all three ground-truth aliases (`BODY~1.ASP`,
  `ECHO~1.ASP`, `VERYLO~1.TXT`) with no extra aliases.
- Fingerprint and structured status output now run after every fallback. This removes the
  contradictory `8.3 oracle: no` followed by `Vulnerable: Yes` that alternate oracles could
  previously produce. JSON/NDJSON status records expose `oracle`, `method`, and
  `probesuffix`, so automation can distinguish `header-signature` from the classic status
  oracle.

## What's new in 1.45

- **Per-extension method-magic validation (best of both worlds).** Method-magic reads a `405`
  from the invalid-method probe as "this resource exists". But some servers/WAFs — and ASP.NET
  extensionless routing — answer `405` to the invalid method for *anything*, so wordlist
  guesses got "confirmed" even though a real GET returns `404` (recovered names that don't
  exist). Rather than the blunt v1.44 whole-oracle downgrade (which lost hidden-file detection
  everywhere it triggered), each `405` is now checked against a **same-extension baseline**
  probed the same way. Because the baseline is per-extension, a requestFiltering-hidden file
  (GET `404`, `_` `405`) is still recovered in the dimensions where `405` is real (e.g. a
  `/bin/*.dll` on a host that only 405s extensionless paths), and false positives are dropped
  only in the exact dimension where the host is 405-for-everything. A non-distinctive `405`
  falls back to the GET-status differential, which still catches served / auth-walled files.

## What's new in 1.44

- **Extension-dimension catch-all guard.** The 1.43 guard covered the file part, but a server
  can enumerate real name prefixes yet still answer the wildcard for *any extension character*,
  exploding into hundreds of never-resolving `ASPNET~1.A / .AA / .AAA …` variants (`1/466
  resolved`). Shortscan now drops extension exploration when >90% of the character set matches
  as valid extension characters, keeping the real extensionless names.

## What's new in 1.43

Three false-positive fixes, all aimed at catch-all / soft-404 / serve-everything front ends:

- **`--retrieve` now percent-encodes the 8.3 alias.** A raw URL-significant byte in a name —
  most dangerously `#` — corrupted the request: `#~2` became a fragment, so the GET silently
  fetched the **directory root** (IIS's `iisstart` welcome page) and the retrieve reported
  those 703 bytes as a high-severity `[8.3-RETRIEVAL]` disclosure. The alias is now built
  through `net/url`, so it targets the literal file (a trailing `::$DATA`/`::$INDEX_ALLOCATION`
  token still survives unescaped).
- **`--mutate-ext` gained a catch-all guard.** It reported *any* `2xx` on `<file>.bak` /
  `.old` / `~` etc. as a "mutation hit"; on a server that answers 200 to everything that meant
  a wall of false hits. It now first probes one impossible sibling extension and bails if that
  also serves.
- **Enumeration is suppressed on catch-all servers.** If the 8.3 character oracle matches an
  implausible fraction (>90%) of the character set as valid first characters, the server is
  answering the wildcard probe for anything — full enumeration would emit hundreds of
  never-resolving garbage short names (`0/133 resolved`). Shortscan now stops with a clear
  warning instead (and saves the wasted requests).

## What's new in 1.42

- **`--maxtime` now defaults to `0` (no limit).** In 1.41 it defaulted to 300s and — because
  a single top-level URL's budget covers its *entire* `-r` recursion — a deep scan could hit
  the limit partway through, drop the still-queued sibling directories, and print a clean
  `Finished!` as if it had completed. It now runs to completion by default, and when a limit
  *is* set and trips, it prints how many queued paths were skipped instead of hiding it.

## What's new in 1.41

- **`--parallel N`** scans several URLs at once (default 10) in **every** output mode. Each
  URL is an independent scan — its own `visited` map and its own recovery knowledge
  (`siblingStems`/`references` are per-scan) — while the shared global caches
  (status/distance/allow-copy/translate/fingerprint/single-stack) stay mutex-guarded.
- **Lean per-host bulk view.** With several hosts in flight, human output is buffered and
  flushed as one contiguous block the moment each scan finishes (so blocks appear in
  completion order and never interleave line-by-line), and each block is rendered **compact**:
  a one-line header `──── <url> ─── VULNERABLE · <oracle>` (or `not vulnerable`), the whole
  fingerprint condensed to one line (`IIS 10.0 · ASP.NET · 8.3:yes · single-stack · DAV:no`),
  then the real findings (SHORTNAMES, disclosures, WebDAV lifts) indented underneath — the
  section rules, `Active:`/`Running:` lines and negative `[REF-CRAWL]`/`[WEBDAV]` chatter are
  dropped. The status bar meanwhile shows an aggregate `[<done>/<total> hosts]` count. A
  **single** host (or `--parallel 1`) keeps the full detailed block as before. `-o json`/`ndjson`
  stream unbuffered because each record already carries its own `url`/`baseurl`. Three `-race`
  regression tests cover the shared globals and the no-interleave guarantee.
- **`--maxtime SECONDS`** is a soft time budget for each top-level URL's whole scan —
  **including its `-r` recursion** — before it stops and moves on. It defaults to `0`
  (**no limit**), because a recursive scan legitimately visits many directories and must
  never be cut short silently; it's opt-in for bulk/`--parallel` runs where one slow or
  tarpit host would otherwise stall the queue. When it does trip, it prints how many queued
  paths it skipped rather than a misleading `Finished!`. In-flight requests are still bounded
  by `-t`.
- **stdin input**: with no positional URL and a piped stdin, newline-delimited URLs are read
  from it — `cat urls.txt | shortscan -o json --parallel 10`. Blank lines and `#` comments
  are skipped.
- **`--auto` is slimmer**: it no longer sweeps the ASP.NET reserved folders
  (`/bin`, `App_Code`, `App_Data`) through `::$INDEX_ALLOCATION` by default. Add `-i`
  (`--auto -i`) to turn the sweep on, or use `--full` for the complete reserved-folder set.
  `--auto`/`--full` now also auto-enable `--fingerprint`.
- **`--fingerprint`** is a conservative per-host stack fingerprint beyond the `Server`
  header: IIS version/sc-substatus from detailed errors, `::$INDEX_ALLOCATION`/cookieless
  routing signals classified without claiming content read, ambiguous mixed/non-IIS front
  ends flagged, WebDAV methods listed as advertised-only, and Allow/COPY confirmed only with
  paired controls. Its probes run concurrently, and a same-origin `--retrieve` is skipped
  when the host is confirmed single-stack IIS (retrieval is a cross-stack-only read).
- **`--custom-sfn SHORTNAME`** is the read complement to `--exact-short`'s existence probe:
  give a custom 8.3 alias **without** `~<digit>` (e.g. `SRC47.TXT`, `DATA47`, `RCFG~A.TXT`)
  plus a base URL, and it GETs the alias — guarded by a random same-extension control — to
  disclose and save the request-filtered file it resolves to. A non-`~digit` alias escapes
  `iiscore!CheckIfShortFileName`, whose 404.0 canonical-mismatch fires only on tilde+digit.
  The alias must already exist on disk (set via `SetFileShortName`; not remotely plantable).
  Standalone by default; with `--auto`/`--full`/`-r` the aliases are probed at every scanned
  directory. Loot lands under `--loot-dir`.
- **`-a allow-copy`** promotes the read-only WebDAV `PROPFIND`/`COPY-in-Allow` differential
  to a first-class autocomplete oracle, for hosts where GET-status is muddied.
- **Live status bar** on stderr — spinner, phase, `[done/total]` queue, request rate and
  found count — auto-disabled when output is redirected, piped, `--quiet`, or non-human, so
  scripted runs stay byte-for-byte identical.
- **Faster start**: the HTTP idle-connection pool is sized to `-c` (killing per-request TLS
  handshakes) and the character-discovery stage runs concurrently, cutting time-to-first-result.
- **Flag names**: `--full-url` (was `--fullurl`), `--is-vuln` (was `--isvuln`), and the
  relax/recurse pair is now `-X`/`--relax` and `-R`/`--backwards-recurse` (`-r` is forward
  `--recurse`). A new ASCII-art banner carries the version.

## What's new in 1.29.2

- Fixed `-i`/`--auto` source-probe URL joining after `::$INDEX_ALLOCATION`: `/bin` and a recovered child now retain their segment boundary (`/bin/file`) instead of becoming `/binfile`. A focused regression covers `DefaultWsdlHelpGenerator.compiled` and nested `App_Data` paths.

## What's new in 1.29.1

- `--exact-short` accepts ordinary `PREFIX~N.EXT` aliases and custom 8.3 candidates such as `SRC47.TXT`, `DATA47`, and `RCFG~A.TXT`. Custom candidates use the direct profile because the late profiles specifically materialize `~N` between the native and managed parser stages.
- `--exact-short-method auto` tries `HEAD`, `OPTIONS`, and `TRACE` in that order for each applicable profile. Every method remains bodyless and must produce a stable candidate/control differential in two full rounds. In the IIS 10 default lab, `HEAD` was `404/404`, while `OPTIONS` confirmed the exact automatic alias as `404/200`; `TRACE` remains a final read-only fallback.
- Structured output separates `aliasverified` from `lfnassociationverified`. A remote differential can verify that an exact alias-like path is special, but it cannot by itself prove which LFN owns that alias. `customsfncandidate` and `canonicalguardbypasscandidate` are therefore candidate labels, not claims of a successful content read.
- `--bitmap-profile DIRECTORY_URL` uses paired `PROPFIND Depth:0` capability controls for `::$INDEX_ALLOCATION`, `::$BITMAP`, and `:$I30:$BITMAP`. It reports `resident-directory-index`, `materialized-directory-index`, or `inconclusive`; it never sends `COPY` or another mutating method.
- `--auto` now invokes that profile only after a calibrated WebDAV capability baseline is available. It is capped at six directories per scan block (`--full`: 24), caches an unavailable origin, skips ADS paths and prioritizes materialized-index directories when `--recurse` is active. It does not guess custom SFNs: custom short-name candidates remain explicit because a normal 8.3 LFN cannot be distinguished from alternate metadata without outside evidence.
- `$BITMAP` is a historical high-water signal, not a current child counter. In the controlled NTFS lab, a directory expanded to 512 children retained `$BITMAP` and a 262,144-byte `$INDEX_ALLOCATION` after 511 children were deleted and after the directory was renamed. Deleting and recreating the directory reset it to a resident index. Long generated names materialized at 3 children in that fixture, while compact 8.3 names needed 8, proving that the threshold depends on index-entry shape.

Examples:

```text
shortscan http://127.0.0.1/sample/ \
  --exact-short RCFG~A.TXT --exact-short SRC47.TXT \
  --exact-short-method auto --exact-short-profile auto

shortscan --bitmap-profile \
  http://127.0.0.1/application/LargeDirectory/
```

The `$BITMAP` profile requires a configuration-dependent WebDAV capability oracle: stable `405` controls without `COPY`, and `COPY` appearing only for a resolving resource. If that baseline is absent, the result is inconclusive rather than guessed from status.

## What's new in 1.27

- Protected-folder index scans no longer try to verify reconstructed LFNs inside the ADS namespace. Shortscan builds a canonical cookieless split-join URL, sends `HEAD`, rejects catch-all 200 responses with two random same-extension siblings, repeats the candidate, and performs a single GET only after confirmation. This works in explicit `-i` and the reserved-folder sweep in `--auto`/`--full`.
- The behavior was validated with matched IIS 10 cells: both enumerate `QUARTE~1.JSO` and `DATABA~1.TXT` inside `App_Data`; only the cell with aggressive cookieless removal restored serves the reconstructed JSON/TXT. The control enumerates the aliases but recovers no LFN or content.
- `--probe-oracle translate` pins `GET` plus `Translate: f` and uses the same two-control + repeat discipline. In the IIS 10 lab, existing ASPX/static files returned 401 while same-extension misses returned 404. This is an existence oracle, not source disclosure. A server that ignores `Translate` may process the GET normally, so the mode is opt-in.
- `--fingerprint` parses detailed IIS substatus/module signals, distinguishes ADS namespace reachability from content read, treats mixed/non-IIS banners as ambiguous, and reports WebDAV methods as advertised-only. Allow/COPY is marked available only after the full positive/negative differential; no mutating method is sent.
- Source-disclosure output is emitted before `Finished!`, and `--auto/--full` now run the same post-enumeration source chain that explicit `-i` already used.

Example: enumerate and retrieve a confirmed `App_Data` LFN only when the split-join is actually live:

```text
shortscan https://example.test/App_Data -i \
  -w appdata.rainbow --autocomplete method --full-url
```

Example: use the `Translate: f` status boundary to verify a known collision group:

```text
shortscan https://example.test/ \
  --probe-candidates --probe-short 'SRCPAG~1.ASP' \
  --probe-oracle translate -w names.txt
```

## What's new in 1.26

- `--probe-oracle allow-copy` pins the probe to `PROPFIND` with `Depth: 0` and `Cache-Control: no-cache`. `--probe-method`, `--probe-status` and `--probe-body-limit` do not determine a match in this mode.
- A hit must be `405` with `COPY`; two random siblings of the same extension and suffix must be stable `405` responses without `COPY`. After removing `COPY`, every other method in `Allow` must agree. The candidate and controls are then repeated before the result is promoted.
- The mode can verify long-name guesses when status and body are otherwise identical, confirm an exact 8.3 ordinal, and carry a calibrated suffix such as `::$INDEX_ALLOCATION`, `::$BITMAP`, or a named ADS like `:Zone.Identifier:$DATA`. It does not disclose file bytes or enumerate unknown long-name/stream-name characters by itself.
- Confirmed in a controlled IIS 10 lab where anonymous PROPFIND was enabled and the WebDAV handler was removed while `WebDAVModule` remained active. Removing both the handler and module at the application root killed the signal; setting `allowAnonymousPropfind=false` at the site level also removed `COPY` from existing and missing paths. This is a configuration-dependent discovery primitive, not a claim that every IIS/WebDAV site is affected.
- No mutating WebDAV method is issued. The tool only inspects the `Allow` header returned to `PROPFIND`.

## What's new in 1.19

- `--webdav` turns a common misconfiguration into full-name recovery. The 8.3 tilde oracle is information-bounded to six prefix + three extension characters, and a patched IIS refuses to serve the alias, so `SECRET~1.ASP` rarely resolves on its own. But when the target announces WebDAV — the module is installed on many legacy/collab/file-serving IIS hosts — an anonymous `PROPFIND Depth:1` on an *allowed* directory returns the full long names of its immediate children as `displayname`/`href`.
- It flags the **hidden-name disclosure**: `PROPFIND` on the parent lists children that requestFiltering hides from a direct `GET` — `web.config`, `/bin`, `App_Data`, `*.bak`/`*.old`/`*.config` — so their names leak even where directory browsing is off. Each recovered name is joined back to the confirmed 8.3 alias it resolves (`AdministratorNotes.txt ← ADMINI~1.TXT`).
- Honest bounds: `Depth:1` is one directory level (`Depth:infinity` is 403 by default), a `PROPFIND` aimed straight at a hidden segment is itself 404, and the *content* of a blocked-extension file stays blocked — this recovers **names**, not blocked content. The technique is WebDAV listing (prior art); the value is first-class integration with the 8.3 scan. Live-confirmed on patched Windows 11 / IIS 10 + WebDAV.
- **1.19.1** fixes the confirmation-status column: in method-magic autocomplete the probe verb is invalid, so IIS answers `405` for *every* file that exists — that is the existence oracle, not the resource's reachability. The recovered name now shows its real `GET` status, so an openly served file reads `200` (and a protected one its true `401`/`403`/`404`), not a misleading `405`. This also makes the column meaningful for telling a servable name from a name that is merely known-to-exist-but-blocked.

## What's new in 1.17

- `--bypass-probe` is a single read-only detector for the whole cookieless "managed-only" native access-control bypass family. Point it at a managed endpoint (`.aspx`/`.asmx`/`.ashx`) to probe it directly, or at a directory to scan first and then probe every endpoint the scan resolves. It splices the token before every path segment (nested apps only blind at one insertion point), and confirms a bypass only when a managed-only form executes the real resource, resolves it distinctly from a non-existent sibling, the canonical form stays blocked, and the invalid lowercase-tag control never executes.
- The differential is classified by baseline status: `401` → native authentication (resource runs anonymously); `403` → ipSecurity (403.503) / require-SSL (403.4) / app-pool isolation (403.18); `404` → requestFiltering. Managed `<authorization>` runs after `RewritePath` and is explicitly not bypassed.
- `--apppool-probe` and `--location-probe` are retained as compatibility aliases of `--bypass-probe`; app-pool isolation and `<location>` control bypasses are now individual classifications of the one probe.
- Confirmation status is shown next to every recovered long name (`200`/`302`/`401`/`403`), so on a real target you can see which endpoints are open, redirecting, or auth-walled. A consistent status palette (2xx green, 3xx cyan, 401/403 yellow, other 4xx/5xx red) is used across the tool, and a `500` crash is never painted as a clean bypass.
- Reliability fixes: the status-based existence oracle escalates its "missing file" baseline with extra probes before trusting an apparent hit (a small 2-probe baseline had produced a live false positive); `auto` autocomplete mode is re-resolved per host so a multi-host `--list` scan no longer inherits the first host's decision; and method-magic autocomplete falls back to a status differential for auth-gated `301/302/401/403` endpoints it would otherwise drop.

## What's new in 1.14

- Reference-derived names now calculate both Windows checksum variants, so a public name such as `PRIMAX5145` can join a hashed alias such as `PR45F4~1` without a rainbow table. Enumerated `.BR`/`.GZ` groups also derive precompressed companions such as `service-worker.js.br`; every derived path still has to pass the configured HTTP oracle.
- Repeatable `--exact-short SHORTNAME` is a standalone exact-alias probe. Since v1.29.1 it accepts every supported 8.3 basename, including custom forms without `~N`. It skips the wildcard vulnerability pre-flight, enumeration, and wordlist configuration entirely, so it remains useful when a WAF blocks `*`, `?`, or a literal `~` and never pays the cost of a large rainbow table.
- Each round sends the exact candidate and two same-length negative aliases. `--exact-short-method auto` uses bodyless `HEAD`, `OPTIONS`, then `TRACE`, stopping at the first stable differential. A result is emitted only when the candidate is stable across `--exact-short-repeats`, both controls are stable and agree, and the candidate's status/header signature differs from them. Throttling and server-error responses are rejected rather than promoted.
- `--exact-short-profile late-encoded` places one cookieless modifier at the application path boundary, splits the candidate immediately before `~N`, fully percent-encodes the managed modifier, and encodes the tilde once as `%7E`. The exact 8.3 alias is therefore absent from the wire representation and is assembled only after the two parser stages. `late` honors the selected session/tilde encodings; `direct` supplies a baseline; `auto` tries `late-encoded`, `late`, then `direct`.
- This mode reports an `alias-differential`, not a recovered long filename. It does not establish which LFN owns the observed path and does not claim a patched-build bypass. Structured output separates `aliasverified`, `lfnassociationverified`, `ordinalverified`, and custom-SFN candidate labels. Two paired controls reduce false positives, but application-specific routing still needs analyst review.
- `--tilde-encoding percent` adds the single-decode `%7E` representation; `all` now rotates through it as well.

## What's new in 1.13

- Wordlists are only parsed after the first vulnerable target is confirmed. Parsing runs in parallel with character-set discovery, and `-V` or a non-vulnerable target never loads the rainbow table.
- Plain/rainbow duplicates are merged case-insensitively, with the checksum-bearing rainbow record taking precedence.
- `--known-extensions` tries the discovered alias directly and pairs matching filename stems with common IIS/ASP.NET extensions, such as `LOGIN~1.ASP`, `LOGIN~1.aspx`, and `Login.aspx`.
- `--probe-candidates` verifies every generated candidate; `--probe-short` selects one or more collision groups through an observed short name.
- `--probe-status` accepts codes and ranges (default `200`). A status is only promoted to a hit when the same status is absent from random, same-extension baseline requests.
- The default brute profile remains constant-memory `GET + status`. For targets where an existing and missing LFN return the same status, `--probe-oracle distance` compares a bounded body against repeated same-extension controls. `--probe-method`, `--probe-suffix`, and `--probe-body-limit` describe the exact read-only profile and are included in structured output.
- Long-name recovery does not pretend to know the NTFS collision ordinal. For example, a verified `PagedList.Mvc.dll` belongs to the `PAGEDL~*.DLL` group, but an HTTP `200` alone cannot prove whether NTFS assigned it `~1` or `~2`. Human output says `ordinal unverified`; JSON/NDJSON/CSV expose `collisiongroup` and `ordinalverified`. Literal alias URLs are still probed per ordinal and are marked verified only if that exact alias path responds as a hit.
- `--candidate-output FILE` writes de-duplicated candidate URLs without probing them, ready for `httpx`, `ffuf`, or another HTTP client.
- Recovered names without an extension are queued for recursive vulnerability validation even when nginx, another reverse proxy, a rewrite, or a protected directory suppresses the usual trailing-slash redirect. Relative and absolute directory redirects are normalized as well. Use `-n` to disable this behavior.
- `--sibling-recovery` reuses only HTTP-confirmed long stems across matching aliases, extensions, and recursively scanned directories on the same origin. A confirmed `COMERCIAL` for `COMERC~1` can therefore seed `COMERCIAL.RAR` when `COMERC~1.RAR` is observed. Every derived path is still verified with the selected autocomplete oracle and remains a collision-group result, never an asserted `~N` mapping.
- `--crawl-references` builds a target-specific candidate set from paths in same-origin HTML, JavaScript, and CSS. The crawler is opt-in, never submits forms, and is bounded by `--crawl-max-pages`, `--crawl-max-depth`, and `--crawl-body-limit`. `--crawl-seed` supplies known pages or assets. Extracted names are only reported as recovered when the normal HTTP oracle confirms them.
- `--reference-only` skips plain/rainbow loading entirely and uses only the bounded target-specific reference set for long-name recovery. It implies `--crawl-references` and is useful when a very large rainbow would cost more than the application-specific crawl.
- Response statistics no longer buffer entire bodies in memory. Disclosure/body matching is bounded, and status/method autocomplete plus candidate probes stop after response headers. This avoids transferring a confirmed `.rar`, `.7z`, `.pfx`, or DLL merely to classify its status.

## Earlier fork enhancements

- `--rate / -r <RPS>` — global request rate limiter (fractional values supported)
- `-w / --wordlist` is now **repeatable** (load several wordlists; duplicates are de-duped)
- Positional URLs accept `@file.txt` to load lines inline
- `-X / --relax` reports tentative matches (Jakarta/CFM/SVC stacks where every status looks like a hit)
- `--proxy <url>` + `--proxy-auth user:pass` (http/https/socks5)
- `-k / --insecure`, `--tls-min 1.0|1.1|1.2|1.3`, `--http2`
- `-A / --user-agent`, `--random-agent`
- `-b / --cookie name=value` (repeatable)
- `--retries N`, `--retry-delay MS` (exponential backoff)
- `--tilde-encoding default|percent|unicode|double|iis-unicode|all` — bypass WAFs that fingerprint `~`
- `--session-style d|x|f|a|empty|rand` — replaces hard-coded `(S(x))` cookieless tokens. `empty` uses the research-derived zero-length modifier `(S())`; the conservative default remains `(S(d))`.
- `--session-encoding literal|outer|asymmetric|asymmetric-full` — percent-encodes cookieless modifiers according to their native/managed parser roles. `outer` encodes both outer pairs; `asymmetric` keeps the first token body raw and encodes every parenthesis of the second; `asymmetric-full` percent-encodes every byte of the second modifier. The default remains `literal`.
- Case-insensitive `bin::$INDEX_ALLOCATION`
- Source-code-disclosure heuristics on resolved files (MZ, PK/ZIP, ASP/ASP.NET source, web.config, PEM, appsettings.json)
- `--output-file FILE`, `--quiet / -q`
- Embedded `dll.txt` ASP.NET wordlist for compiled-page enumeration
- New path suffixes: `.cshtml`, `.vbhtml`, `.razor`, `.svc`, `.ashx`, `.config`
- NTFS ADS variants: also probes `::$DATA`, `:$i30:$INDEX_ALLOCATION` (case variants)
- `--mutate-ext` — after every confirmed hit, also probes `.bak/.old/.orig/.swp/.txt/~/.disabled/.1/.copy/.save`
- `-o ndjson` and `-o csv` output formats
- Graceful `SIGINT` handling (Ctrl-C flushes partial state)
- Unit test suite + GitHub Actions CI
- `-r` now means `--recurse` (forward recursion, opt-in as of v1.16.0); `-R`/`--backwards-recurse` ascends into parent directories. The rate limiter is `--rate` (long form only)

## Functionality

Shortscan is designed to quickly determine which files with short filenames exist on an IIS webserver. Once a short filename has been identified the tool will try to automatically identify the full filename.

In addition to standard discovery methods Shortscan also uses a unique checksum matching approach to attempt to find the long filename where the short filename is based on Windows' proprietary shortname collision avoidance checksum algorithm (more on this research at a later date).

## Installation

### Quick install

Using a recent version of [go](https://golang.org/):

```
go install github.com/thezakman/shortscan/cmd/shortscan@latest
```

### Manual install

To build (and optionally install) locally:

```
go get && go build
go install
```

## Usage

### Basic usage

Shortscan is easy to use with minimal configuration. Basic usage looks like:

```
$ shortscan http://example.org/
```

### Examples

This example sets multiple custom headers by using `--header`/`-H` multiple times:
```
shortscan -H 'Host: gibson' -H 'Authorization: Basic ZGFkZTpsMzN0'
```

To check whether a site is vulnerable without performing file enumeration use:
```
shortscan --is-vuln https://www.example.org/
```

To scan many hosts at once, pipe a list on stdin and fan out with `--parallel`:
```
cat hosts.txt | shortscan --parallel 10 --maxtime 300
```

To test for Source Code Disclosure in ASP.NET `::$INDEX_ALLOCATION` and `:$i30:$INDEX_ALLOCATION` vulnerabilities:
```
shortscan http://www.example.org/bin -i -w ~/wordlists/rainbow/dll.rainbow --full-url --autocomplete method
```

If a proxy or path-signature rule blocks the literal cookieless form, retry the
confirmed disclosure path with the parser-aware asymmetric representation:

```
shortscan http://www.example.org/bin -i \
  --session-style empty \
  --session-encoding asymmetric \
  -w ~/wordlists/rainbow/dll.rainbow --full-url
```

The first modifier is emitted as `%28S()%29`; the second as
`%28S%28%29%29`. This is an evasion representation for an already vulnerable
pipeline, not a bypass for a fully patched ASP.NET Framework installation.
Use `--session-encoding asymmetric-full` to emit the second modifier as
`%28%53%28%29%29`. Both forms were validated against the same byte-identical
artifact; the fully encoded form increases representation diversity without
changing the underlying vulnerability or patch status.

To test a known exact 8.3 alias without DOS wildcards or response bodies:

```
shortscan https://www.example.org/Content/images/ \
  --exact-short 'IMAGEM~1.JPG' \
  --exact-short-profile auto \
  --exact-short-method auto \
  --exact-short-repeats 3 \
  --full-url
```

The first `auto` profile emits a path shaped like:

```
/%28S(d)%29/Content/images/IMAGEM/%28%53%28%64%29%29%7E1.JPG
```

The native filter consumes the first standalone modifier. After one decode,
the managed modifier is removed and its surrounding slash is joined, yielding
`/Content/images/IMAGEM~1.JPG` late in the pipeline. Each round also probes two
same-length aliases such as `IMAGEZ~1.JPG` and `IMAGEQ~1.JPG`. A stable
candidate/control difference is useful evidence of exact-alias handling, but
it does not recover the LFN or prove that a guessed long filename owns `~1`.
For a nested ASP.NET application, set its boundary explicitly, for example
`--exact-short-app-root /webform/`; the target directory must be below it.
Use `-o ndjson` or `-o csv` to feed the result to another tool.

To test whether a cookieless managed-only token bypasses a native, `<location>`-scoped
control (authentication, ipSecurity, requestFiltering, require-SSL or app-pool
isolation), point `--bypass-probe` at the guarded managed endpoint:

```
shortscan --bypass-probe https://www.example.org/secure/Panel.aspx
```

Give it a directory instead and it scans first, then probes every managed-handler
endpoint the scan resolves:

```
shortscan --bypass-probe -w names.rainbow https://www.example.org/secure/
```

The probe is read-only. It only reports a candidate when a managed-only form
executes the real resource and resolves it distinctly from a non-existent sibling,
while the canonical form stays blocked and the invalid lowercase-tag control never
executes. The baseline status names the likely native control, and the confirmation
(FREB/substatus, or an `APP_POOL_ID` echo for an app-pool crossing) is left to the
analyst. `--apppool-probe` and `--location-probe` are aliases of this mode.

To pivot from a verified long stem into related archives, certificate
containers, backups, or the same alias prefix below a recursively scanned
directory:

```
shortscan --sibling-recovery -w names.rainbow https://www.example.org/
```

For example, after confirming `COMERCIAL` from `COMERC~1`, an observed
`COMERC~1.RAR` adds `COMERCIAL.RAR` as a high-priority `sibling-stem`
candidate. The request still has to satisfy the normal method, status, or
distance oracle before it is reported.

When the target advertises WebDAV, recover the full long names past the 6+3
truncation and flag the requestFiltering-hidden ones:

```
shortscan --webdav https://www.example.org/app/
```

Any confirmed 8.3 alias is tied to the full name `PROPFIND` recovers
(`AdministratorNotes.txt ← ADMINI~1.TXT`), and children a direct `GET` refuses
— `web.config`, `/bin`, `App_Data`, `*.bak`/`*.config` — are marked
`[HIDDEN-NAME/high]`. It recovers names, not blocked file content.

To turn public application references into a small target-specific wordlist:

```
shortscan --crawl-references \
  --crawl-seed /sis_erp/sis.login.aspx \
  --crawl-max-pages 24 \
  --crawl-max-depth 2 \
  http://www.example.org/
```

For example, an HTML reference to `sis/login.js` followed by the JavaScript
literal `sis.seguranca.wprecuperasenha.aspx` adds the path components and full
filename as `reference` candidates. Only same-origin `GET` requests are made;
forms are not submitted, cross-origin assets are ignored, and each response is
limited to `--crawl-body-limit` bytes. The target base URL is always a seed, so
`--crawl-seed` is needed only for additional known pages/assets.
References are also checksummed in memory. This lets a literal such as
`PRIMAX5145` become a `reference-checksum` candidate for `PR45F4~1`, even
though the classic six-character prefix no longer appears in the hashed alias.
Modern and Windows Server 2003/XP checksum variants are considered, and the
candidate still has to pass the selected HTTP oracle before it is reported.
For enumerated `.BR` and `.GZ` aliases, public asset references also produce
precompressed companions: `service-worker.js` can seed
`service-worker.js.br` as a `reference-compressed` candidate. This is useful
for PWA/Workbox/Blazor deployments where compressed artifacts are present on
disk but are not linked directly.
Use `--reference-only` in the same command to avoid loading any configured
rainbow table.

Large custom rainbow tables are deferred automatically. This command returns without parsing the table when the target is not vulnerable:

```
shortscan -w huge-custom.rainbow https://www.example.org/
```

To augment normal autocomplete with common full extensions (`LOGIN~1.ASP` can yield `Login.aspx`):

```
shortscan --known-extensions -w names.txt https://www.example.org/
```

To probe every long-name candidate and accept only a `200` response that differs from the same-extension baseline:

```
shortscan --probe-candidates --probe-status 200 -w names.txt https://www.example.org/
```

Use a previously calibrated same-status exact-LFN profile (example only; the
working method and suffix are target-specific):

```
shortscan --probe-candidates \
  --probe-status 404 \
  --probe-oracle distance \
  --probe-method OPTIONS \
  --probe-suffix '/~1.rem' \
  --probe-body-limit 4096 \
  -w names.txt https://www.example.org/
```

The distance mode samples random files with the same extension, method, and
suffix before promoting a same-status body difference. It never reads more than
`--probe-body-limit` bytes per response. `--probe-method` is deliberately
restricted to `GET`, `HEAD`, `OPTIONS`, `TRACE`, `DEBUG`, `PROPFIND`, and `_`;
the recovery workflow will not issue a mutating WebDAV/HTTP method.

When a WebDAV/StaticFile conflict makes existing and missing candidates both
return 405, use the capability-header oracle:

```text
shortscan --probe-candidates \
  --probe-short 'PAGEDL~1.DLL' \
  --probe-oracle allow-copy \
  -w names.rainbow https://www.example.org/
```

`allow-copy` always sends read-only `PROPFIND Depth:0`; it never sends `COPY`.
For a previously calibrated directory-attribute cell, the same controlled
oracle can be carried in a suffix:

```text
shortscan --probe-candidates \
  --probe-short 'LARGED~1' \
  --probe-oracle allow-copy \
  --probe-suffix '::$BITMAP' \
  -w names.txt https://www.example.org/
```

The same mechanism can verify a known or wordlist-derived NTFS named stream
without retrieving its bytes:

```text
shortscan --probe-candidates \
  --probe-short 'SERVIC~1.BR' \
  --probe-oracle allow-copy \
  --probe-suffix ':Zone.Identifier:$DATA' \
  -w names.txt https://www.example.org/
```

Select recovery groups through one or more enumerated short names by repeating `--probe-short`:

```
shortscan --probe-candidates \
  --probe-short 'LOGIN~1.ASP' \
  --probe-short 'APP~1.DLL' \
  -w names.rainbow https://www.example.org/
```

If `APP~1.DLL` and `APP~2.DLL` share the same six-character stem and extension,
the long-name candidates are tested once as `APP~*.DLL`; selecting either alias
does not assert a one-to-one ordinal mapping.

Generate candidate URLs without sending the candidate `GET` requests, then validate them with another tool:

```
shortscan -a none --candidate-output candidates.txt -w names.txt https://www.example.org/
httpx -l candidates.txt -mc 200
```

### Advanced features

Run the built binary for the complete, version-matched option list:

```
shortscan --help
```

### Code layout

The scanner package is split by responsibility. Go compiles all files in the
same `package shortscan` together, so this is modular without adding runtime
indirection:

```
cli.go          command-line parsing, validation and dispatch
transport.go    HTTP client, retries, rate limiting and bounded reads
wordlist.go     deferred plain/rainbow loading
cookieless.go   session modifiers and disclosure-path rewriting
recovery.go     autocomplete, candidate-probe and response oracles
allowcopy.go    read-only WebDAV Allow/COPY differential
translate.go    paired Translate:f exact-LFN differential
sibling.go      verified sibling-stem knowledge
collision.go    checksum-mask and collision-ancestry long-name reconstruction
references.go   bounded HTML/JS/CSS reference recovery
aliasprobe.go   standalone --exact-short bodyless alias differential
bitmapprofile.go read-only $BITMAP directory-index/high-water profile
bypass.go       unified --bypass-probe cookieless native-control bypass
source.go       --retrieve direct 8.3 disclosure and --source-probe chain
indexchain.go   -i/--full reserved ASP.NET folder ::$INDEX_ALLOCATION sweep
fingerprint.go  conservative IIS/ASP.NET/WebDAV signal classification
customsfn.go    --custom-sfn custom short-name content read
peinspect.go    inline PE/.NET metadata summary for disclosed assemblies
webdav.go       --webdav PROPFIND Depth:1 full-name lift and hidden-name flag
progress.go     live stderr status bar + per-host --parallel output buffering
output.go       human and structured output
shortscan.go    short-name enumeration and scan orchestration
```

Supporting library packages live alongside the scanner:

```
pkg/hashrecover  meet-in-the-middle inversion of the 16-bit collision checksum
pkg/shortutil    8.3 name/checksum generation and the shortutil CLI
pkg/dotnetmeta   dependency-free .NET assembly metadata reader (shortloot / peinspect)
pkg/levenshtein  edit-distance oracle for response-body comparison
pkg/maths        small integer helpers
```

## Utility

The shortscan project includes a utility named `shortutil` which can be used to perform various short filename operations and to make custom rainbow tables for use with the tool.

### Examples

You can create a rainbow table from an existing wordlist like this:

```
shortutil wordlist input.txt > output.rainbow
```

To generate a one-off checksum for a file:

```
shortutil checksum index.html
```

### Usage

Run `shortutil <command> --help` for a definitive list of options for each command.

```
Shortutil v0.6 · a short filename utility by bitquark & TheZakMan
Usage: shortutil <command> [<args>]

Options:
  --help, -h             display this help and exit

Commands:
  wordlist               add hashes to a wordlist for use with, for example, shortscan
  checksum               generate a one-off checksum for the given filename
```

### shortloot

The project also ships `shortloot`, a dependency-free .NET assembly analyzer for the
DLLs `--retrieve`/`--source-probe`/`-i` disclose (saved under `--loot-dir`). It reads
the PE/CLI metadata without loading the assembly and dumps the build/PDB path, the
`#Strings` heap (namespace/type/method/field names) and the `#US` heap (string literals
— a compiled page's static HTML and any hard-coded secrets):

```
shortloot --all App_Web_s3cr3t.dll
shortloot --literals --grep "password,server=" *.dll
```

## Wordlist

A custom wordlist was built for shortscan. For full details see [pkg/shortscan/resources/README.md](pkg/shortscan/resources/README.md)

## Credit

Original IIS short filename [research](https://soroush.secproject.com/downloadable/microsoft_iis_tilde_character_vulnerability_feature.pdf) by Soroush Dalili.

Source Code Disclosure in ASP.NET [research](https://swarm.ptsecurity.com/source-code-disclosure-in-asp-net-apps/) by Arseniy Sharoglazov.

Implementation of the `-i` feature by [ke0ge](https://github.com/ke0ge/).

Additional research and this project by [bitquark](https://github.com/bitquark).
