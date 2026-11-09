#!/bin/bash
# Usage: run_capped.sh NAME WORKDIR cmd...
# Caps: systemd user scope MemoryMax=6G MemorySwapMax=0 CPUQuota=200%; taskset 2 CPUs; CPU 120 s; wall 140 s.
# The Lean toolchain and the read-only Mathlib cache are put on PATH / LEAN_PATH; the rest of the env is cleared.
set -u
R=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/bsymbol-review-r1
NAME=$1; WD=$2; shift 2
L=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
LP="$R/build"; for d in $P/*/.lake/build/lib/lean; do LP="$LP:$d"; done
start=$(date -u +%FT%T.%NZ); t0=$(date +%s.%N)
cd "$WD"
systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0 -p CPUQuota=200% \
  env -i PATH=$L:/usr/bin:/bin LANG=C.UTF-8 LEAN_PATH="$LP" HOME=/tmp \
  taskset -c 0,1 prlimit --cpu=120 timeout -s KILL 140 "$@" > "$R/logs/$NAME.stdout" 2> "$R/logs/$NAME.stderr"
rc=$?
t1=$(date +%s.%N)
printf '{"name":"%s","utc_start":"%s","returncode":%d,"wall_seconds":%s,"cmd":"%s","caps":"systemd user scope MemoryMax=6G MemorySwapMax=0 CPUQuota=200%%; taskset 0,1; prlimit cpu 120 s; timeout 140 s"}\n' "$NAME" "$start" $rc "$(echo "$t1 - $t0" | bc)" "$*" > "$R/logs/$NAME.receipt.json"
cat "$R/logs/$NAME.receipt.json"
