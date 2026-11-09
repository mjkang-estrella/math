#!/usr/bin/env bash
# fetch.sh <label> <url> : one capped curl into a fresh empty directory fetch/<label>/ ; never retries.
set -u
R=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/chanlevine-review-r1
label=$1; url=$2; d=$R/fetch/$label
if [ -e "$d" ]; then echo "exists: $d (no refetch)"; exit 2; fi
mkdir -p "$d"
start=$(date -u +%Y-%m-%dT%H:%M:%SZ)
( ulimit -t 120; ulimit -v 6291456; timeout 60 curl -sS -A "independent-review-script/1.0 (no-contact)" --max-time 50 --max-filesize 20000000 -D "$d/headers.txt" -o "$d/body" -w '%{http_code}' "$url" ) > "$d/http_code" 2> "$d/curl.stderr"
rc=$?
code=$(cat "$d/http_code")
sha=$(sha256sum "$d/body" 2>/dev/null | cut -d' ' -f1)
printf '{"label":"%s","url":"%s","start_utc":"%s","curl_exit":%d,"http_code":"%s","body_sha256":"%s","body_bytes":%s}\n' "$label" "$url" "$start" $rc "$code" "$sha" "$(stat -c %s "$d/body" 2>/dev/null || echo 0)" > "$d/receipt.json"
cat "$d/receipt.json"
