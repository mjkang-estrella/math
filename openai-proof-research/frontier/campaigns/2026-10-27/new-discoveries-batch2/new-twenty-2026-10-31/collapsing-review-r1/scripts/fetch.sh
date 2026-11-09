#!/bin/bash
# usage: fetch.sh NAME URL  -> sources/prior/NAME/raw + receipt (single attempt, no retries)
R=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/collapsing-review-r1
D=$R/sources/prior/$1; mkdir -p $D
UTC=$(date -u +%FT%TZ)
OUT=$(curl -sS -L --max-time 60 -A "Mozilla/5.0 (academic literature review)" -o $D/raw -w '%{http_code} %{url_effective} %{content_type}' "$2" 2>&1)
set -- "$1" "$2" $OUT
printf '{"name":"%s","url":"%s","utc":"%s","status":"%s","final_url":"%s","content_type":"%s","bytes":%s,"sha256":"%s"}\n' "$1" "$2" "$UTC" "$3" "$4" "$5" "$(stat -c %s $D/raw 2>/dev/null || echo 0)" "$(sha256sum $D/raw | cut -d' ' -f1)" > $D/receipt.json
cat $D/receipt.json
