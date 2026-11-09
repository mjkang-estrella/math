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
fetch source-abs 'https://arxiv.org/abs/2603.12770'
fetch source-html 'https://arxiv.org/html/2603.12770v1'
fetch companion-repository 'https://www.math.wvu.edu/~hlai2/Pdf/Hong-Jian_Lai_Pdf/318_DM_2023.pdf'
fetch openalex-search 'https://api.openalex.org/works?search=2603.12770&per-page=10'
fetch companion-openalex 'https://api.openalex.org/works/https://doi.org/10.1016/j.disc.2023.113402'
fetch dong-publications 'https://math.nie.edu.sg/fmdong/Research/Publications-Dong.htm'
fetch openai-head 'https://api.github.com/repos/openai/math/commits/HEAD'
fetch omega-head 'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'
