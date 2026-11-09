#!/bin/bash
set -u
LANE_DIR=$(cd -- "$(dirname -- "$0")/.." && pwd)
export TMPDIR="$LANE_DIR/tmp" XDG_CACHE_HOME="$LANE_DIR/cache"
fetch() {
 local key="$1" url="$2"
 mkdir "$LANE_DIR/downloads/$key" || return
 date -u +%FT%TZ > "$LANE_DIR/downloads/$key/receipt.txt"
 printf '%s\n' "$url" >> "$LANE_DIR/downloads/$key/receipt.txt"
 curl -L --max-time 22 --connect-timeout 12 -D "$LANE_DIR/downloads/$key/headers.txt" -o "$LANE_DIR/downloads/$key/body" -w 'HTTP %{http_code} bytes %{size_download}\n' "$url" >> "$LANE_DIR/downloads/$key/receipt.txt" 2> "$LANE_DIR/downloads/$key/curl.log"
 printf 'curl_exit %s\n' "$?" >> "$LANE_DIR/downloads/$key/receipt.txt"
 test ! -f "$LANE_DIR/downloads/$key/body" || sha256sum "$LANE_DIR/downloads/$key/body" >> "$LANE_DIR/downloads/$key/receipt.txt"
}
fetch openalex-title 'https://api.openalex.org/works?search=Every%203-connected%20split%20graph%20of%20order%20at%20least%2013%20is%20Hamilton-connected&per-page=10'
fetch companion-citing 'https://api.openalex.org/works?filter=cites:W4324056420&per-page=50'
fetch arxiv-listing 'https://arxiv.org/list/math.CO/2026-11?show=2000'
