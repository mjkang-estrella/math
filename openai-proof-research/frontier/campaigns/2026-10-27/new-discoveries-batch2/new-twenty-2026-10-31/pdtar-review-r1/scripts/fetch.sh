#!/usr/bin/env bash
# fetch.sh URL OUTNAME  -- single polite GET, no retry; receipt appended to sources/web/receipts.txt
LANE="$(cd "$(dirname "$0")/.." && pwd)"
URL="$1"; OUT="$LANE/sources/web/$2"
CODE=$(curl -sS -L --max-time 40 -A "pdtar-review-r1 research fetch (no retries)" -o "$OUT" -w '%{http_code}' "$URL")
SHA=$(sha256sum "$OUT" | cut -d' ' -f1); SZ=$(stat -c %s "$OUT")
echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) $CODE $SHA ${SZ}B $URL -> $2" | tee -a "$LANE/sources/web/receipts.txt"
