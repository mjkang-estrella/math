#!/bin/bash
# fetch arXiv e-print source bundles with polite delay; record receipts (utc id http sha256 filetype)
cd "$(dirname "$0")/.."
mkdir -p sources/eprint
for a in "$@"; do
  f=sources/eprint/$a.bin
  [ -s "$f" ] && continue
  code=$(curl -sS -L --max-time 60 -A 'Mozilla/5.0 (research; polite)' -o "$f" -w '%{http_code}' "https://arxiv.org/e-print/$a")
  echo "$(date -u +%FT%TZ) $a $code $(sha256sum "$f"|cut -c1-64) $(file -b "$f"|cut -c1-60)" >> sources/receipts-eprint.txt
  sleep 4
done
