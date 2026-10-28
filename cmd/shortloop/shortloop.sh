#!/usr/bin/env bash
# shortloop — iterative shortname discovery loop, exactly the staged idea:
#   round 0 : crawl the target for real names -> dynamic wordlist
#   round N : scan (everything + the dynamic wordlist); collect recovered/reachable files;
#             crawl ONLY the newly-reached files for more references -> grow the wordlist;
#             stop when a round reaches nothing new (dedup tracked, so no infinite recursion).
#
# Usage: shortloop.sh <target-url> [max-rounds]
#   env: SS=path/to/shortscan  SG=path/to/shortgen  (default: alongside this script's repo root)
set -u
TARGET="${1:?usage: shortloop.sh http://host/path/ [max-rounds]}"
MAXR="${2:-6}"
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
SS="${SS:-$ROOT/shortscan}"
SG="${SG:-$ROOT/shortgen}"
SSFLAGS="${SSFLAGS:---auto}"   # override to control which techniques run, e.g. "--known-extensions --collision-ancestry"
CURL="/usr/bin/curl -sS -m 10 --path-as-is"

WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
WL="$WORK/words.txt"; CRAWLED="$WORK/crawled.txt"; FOUND="$WORK/found.txt"
: > "$WL"; : > "$CRAWLED"; : > "$FOUND"

crawl(){ "$SG" -url "$1" 2>/dev/null >> "$WL"; echo "$1" >> "$CRAWLED"; }

echo "[shortloop] target=$TARGET  rounds<=$MAXR"
echo "[round 0] crawl target for real names"
crawl "$TARGET"
sort -u -o "$WL" "$WL"
echo "  wordlist: $(wc -l < "$WL" | tr -d ' ') names"

for r in $(seq 1 "$MAXR"); do
  echo "[round $r] scan (--auto -w wordlist[$(wc -l < "$WL" | tr -d ' ')])"
  OUT="$WORK/scan_$r.ndjson"
  "$SS" "$TARGET" $SSFLAGS -w "$WL" -a status -o ndjson --timeout 12 > "$OUT" 2>/dev/null
  # reachable recovered full names (2xx/3xx) -> crawlable URLs
  python3 - "$OUT" "$TARGET" > "$WORK/reach_$r.txt" <<'PY'
import sys, json
out, target = sys.argv[1], sys.argv[2]
seen=set()
for line in open(out, errors="ignore"):
    try: o=json.loads(line)
    except: continue
    if not (o.get("fullmatch") and o.get("fullname")): continue
    try: st=int(o.get("status") or 0)
    except: st=0
    base=o.get("baseurl") or target
    if 200<=st<400:
        u=base+o["fullname"]
        if u not in seen: seen.add(u); print(u)
PY
  sort -u "$WORK/reach_$r.txt" >> "$FOUND"; sort -u -o "$FOUND" "$FOUND"
  # new reachable files we have NOT crawled yet
  comm -23 <(sort -u "$WORK/reach_$r.txt") <(sort -u "$CRAWLED") > "$WORK/new_$r.txt"
  N=$(grep -c . "$WORK/new_$r.txt" || true)
  echo "  recovered-reachable this round: $(grep -c . "$WORK/reach_$r.txt" || true) (new to crawl: $N)"
  if [ "$N" -eq 0 ]; then echo "  converged — nothing new to crawl"; break; fi
  while read -r u; do [ -n "$u" ] && crawl "$u"; done < "$WORK/new_$r.txt"
  sort -u -o "$WL" "$WL"
done

echo "[done] reachable files discovered:"; sort -u "$FOUND" | sed 's/^/  /'
echo "[done] final wordlist: $(wc -l < "$WL" | tr -d ' ') names"
