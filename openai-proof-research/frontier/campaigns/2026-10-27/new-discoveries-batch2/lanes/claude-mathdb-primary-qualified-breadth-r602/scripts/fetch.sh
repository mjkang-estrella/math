#!/bin/bash
# fetch.sh URL OUTFILE : one request, generic User-Agent only, no cookies/referer/personal data; logs to fetch-log.tsv
set -u
URL="$1"; OUT="$2"; mkdir -p "$(dirname "$OUT")"
CODE=$(curl -sS -L --max-time 60 --proto '=https' -A 'Mozilla/5.0 (X11; Linux x86_64) generic-research-fetch/1.0' -o "$OUT" -w '%{http_code}' "$URL" 2>>fetched/fetch-stderr.txt)
SZ=$(stat -c %s "$OUT" 2>/dev/null || echo 0); SH=$(sha256sum "$OUT" 2>/dev/null | cut -c1-64)
printf "%s\t%s\t%s\t%s\t%s\n" "$(date -u +%FT%TZ)" "$CODE" "$SH" "$SZ" "$URL" >> fetch-log.tsv
echo "$CODE $SZ $SH"
