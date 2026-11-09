#!/bin/bash
# usage: fetch.sh NAME URL  -> downloads/NAME + receipts/NAME.receipt.json (one attempt, no retry)
cd "$(dirname "$0")/.."; N=$1; U=$2
code=$(curl -sS -L --max-time 60 -A "Mozilla/5.0 (research review; single request)" -o "downloads/$N" -w '%{http_code}' "$U")
sha=$(sha256sum "downloads/$N" 2>/dev/null | cut -d' ' -f1); sz=$(stat -c %s "downloads/$N" 2>/dev/null)
printf '{"url": "%s", "utc": "%s", "http_status": %s, "sha256": "%s", "bytes": %s}\n' "$U" "$(date -u +%FT%TZ)" "$code" "$sha" "${sz:-0}" > "receipts/$N.receipt.json"
cat "receipts/$N.receipt.json"
