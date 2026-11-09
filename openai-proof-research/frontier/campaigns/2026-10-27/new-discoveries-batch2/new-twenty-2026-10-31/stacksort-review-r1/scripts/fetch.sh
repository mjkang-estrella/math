#!/bin/bash
# Usage: scripts/fetch.sh <name> <url>   -> dl-r1/<name>/ (fresh dir), body + headers + receipt line
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"
name="$1"; url="$2"; d="$LANE/dl-r1/$name"
[ -e "$d" ] && { echo "exists: $d"; exit 1; }
mkdir -p "$d"
code=$(curl -sS -L --max-time 60 --max-filesize 30000000 -A "research-review-client/1.0" -D "$d/headers.txt" -o "$d/body" -w '%{http_code}' "$url")
sha=$(sha256sum "$d/body" | cut -d' ' -f1); sz=$(stat -c %s "$d/body")
printf '{"name":"%s","url":"%s","utc":"%s","status":%s,"bytes":%s,"sha256":"%s"}\n' "$name" "$url" "$(date -u +%FT%TZ)" "$code" "$sz" "$sha" | tee "$d/receipt.json" >> "$LANE/dl-r1/receipts.jsonl"
