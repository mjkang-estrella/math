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
fetch source-citing 'https://api.openalex.org/works?filter=cites:W7136485224&per-page=100'
fetch openai-tree 'https://api.github.com/repos/openai/math/git/trees/4eaee87548250b2682affda7d05d947c05554bae?recursive=1'
fetch omega-tree 'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/2c54932b6f9a7eb9a838e5be71e91d97e10027be?recursive=1'
