#!/bin/bash
# fetch arXiv abs pages with polite delay; record receipts
cd "$(dirname "$0")/.."
python3 -I -c "import json;d=json.load(open('extracted.json'));print('\n'.join(i+' '+o['source_url'] for i,o in d.items()))" | sort -u -k2 | while read id url; do
  a=${url##*/abs/}; f=sources/abs-$a.html
  [ -s "$f" ] && continue
  code=$(curl -sS -L --max-time 30 -A 'Mozilla/5.0 (research; polite)' -o "$f" -w '%{http_code}' "https://arxiv.org/abs/$a")
  echo "$(date -u +%FT%TZ) $id $a $code $(sha256sum "$f"|cut -c1-64)" >> sources/receipts-abs.txt
  sleep 4
done
