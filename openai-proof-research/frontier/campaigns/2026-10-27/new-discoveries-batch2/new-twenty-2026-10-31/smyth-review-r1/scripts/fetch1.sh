#!/bin/bash
# fetch1.sh NAME URL : one GET with TLS verification ON (curl default), into dl/NAME/ (fresh, must not exist), with receipt.
# Never retried; 403/429/challenge recorded and not repeated.
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/smyth-review-r1
NAME=$1; URL=$2; D=$L/dl/$NAME
mkdir "$D" || { echo "dir exists, refusing (no retries)"; exit 2; }
cd "$D"
UTC=$(date -u +%FT%TZ)
OUT=$(timeout 45 curl -sS -L --max-time 40 --max-redirs 5 -A 'research-review-lane/1.0' -H 'Accept: */*' -o body -D headers.txt -w '%{http_code} %{url_effective} %{size_download} %{content_type}' "$URL" 2>curl.stderr); RC=$?
read CODE FINAL SIZE CTYPE <<< "$OUT"
SHA=$(sha256sum body 2>/dev/null | cut -d' ' -f1)
printf '{"url": "%s", "utc": "%s", "curl_rc": %s, "http_status": "%s", "final_url": "%s", "bytes": "%s", "content_type": "%s", "sha256": "%s", "tls_verification": "on (curl default)"}\n' "$URL" "$UTC" "$RC" "$CODE" "$FINAL" "$SIZE" "$CTYPE" "$SHA" > receipt.json
cat receipt.json
