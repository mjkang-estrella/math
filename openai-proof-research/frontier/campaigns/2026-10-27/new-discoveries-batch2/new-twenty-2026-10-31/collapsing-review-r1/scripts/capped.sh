#!/bin/bash
# usage: capped.sh LOGPREFIX cmd args...   -- runs under 2 CPUs, MemoryMax=6G, CPU 120 s, wall 140 s, AS 64 GiB
set -u
LOG=$1; shift
START=$(date -u +%FT%TZ)
systemd-run --user --scope --quiet -p MemoryMax=6G -p MemorySwapMax=0 -p CPUQuota=200% \
  taskset -c 0,1 prlimit --cpu=120 --as=68719476736 timeout -k 5 140 "$@" > "$LOG.stdout" 2> "$LOG.stderr"
RC=$?
END=$(date -u +%FT%TZ)
printf '{"cmd":"%s","start_utc":"%s","end_utc":"%s","exit":%d,"stdout_sha256":"%s","stderr_sha256":"%s","caps":"systemd scope MemoryMax=6G MemorySwapMax=0 CPUQuota=200%%; taskset 0,1; prlimit cpu=120 as=64GiB; timeout 140"}\n' \
  "$(echo "$*" | sed 's/"/\\"/g')" "$START" "$END" $RC "$(sha256sum < "$LOG.stdout" | cut -d' ' -f1)" "$(sha256sum < "$LOG.stderr" | cut -d' ' -f1)" > "$LOG.receipt.json"
echo "exit=$RC"
exit $RC
