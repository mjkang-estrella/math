#!/bin/bash
# fetch.sh OUTDIR LOG id...   ; one attempt each, no retries; abort batch on 403/429/challenge
D=$1; LOG=$2; shift 2
for a in "$@"; do
  f="$D/$a.pdf"; [ -s "$f" ] && { echo "skip $a" ; continue; }
  t=$(date -u +%FT%TZ)
  code=$(curl -sS --max-time 40 -A "Mozilla/5.0 (research screening; single request)" -o "$f.part" -w '%{http_code} %{url_effective} %{content_type}' "https://arxiv.org/pdf/$a" 2>>"$LOG.stderr")
  rc=$?
  set -- $code; hc=$1
  if [ "$rc" = 0 ] && [ "$hc" = 200 ] && head -c 5 "$f.part" | grep -q '%PDF'; then mv "$f.part" "$f"; echo "$t $a OK $code $(sha256sum "$f"|cut -c1-64) $(stat -c%s "$f")" >> "$LOG"
  else echo "$t $a FAIL rc=$rc $code" >> "$LOG"; mv "$f.part" "$D/failed-$a.bin" 2>/dev/null
    case "$hc" in 403|429) echo "STOP on $hc" >> "$LOG"; exit 3;; esac
  fi
  sleep 1.5
done
