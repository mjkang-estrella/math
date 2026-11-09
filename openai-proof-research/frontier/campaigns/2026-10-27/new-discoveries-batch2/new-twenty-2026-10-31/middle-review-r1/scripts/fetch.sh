#!/bin/bash
# Polite single fetch with receipt. Usage: fetch.sh <outname> <url>
# Never retries; records HTTP status, bytes and sha256 in downloads/receipts.jsonl.
set -u
R=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1
DL=$R/downloads
name=$1; url=$2
t=$(date -u +%Y-%m-%dT%H:%M:%SZ)
code=$(curl -sS -L --max-time 40 -A "research-review-script/1.0 (no-reply)" -o "$DL/$name" -w '%{http_code}' "$url")
sz=$(stat -c %s "$DL/$name" 2>/dev/null || echo 0)
sha=$(sha256sum "$DL/$name" 2>/dev/null | cut -d' ' -f1)
printf '{"utc":"%s","url":"%s","file":"%s","http":"%s","bytes":%s,"sha256":"%s"}\n' "$t" "$url" "$name" "$code" "$sz" "$sha" >> "$DL/receipts.jsonl"
echo "$code $sz $name"
sleep 2
