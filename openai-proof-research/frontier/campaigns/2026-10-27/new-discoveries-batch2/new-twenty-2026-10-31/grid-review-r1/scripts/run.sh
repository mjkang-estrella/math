#!/usr/bin/env bash
# Capped single-process runner for lane grid-review-r1 (written for this lane; not reused).
# Usage: run.sh NAME script.py [args...]
# Caps: 2 CPUs (taskset 0,1), CPU 120 s (RLIMIT_CPU), wall 140 s (timeout),
# address space 2 GiB (RLIMIT_AS), MALLOC_ARENA_MAX=2, python3 -I, lane-local TMPDIR.
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"
NAME="$1"; shift
LOG="$LANE/logs/$NAME.log"; TIMEF="$LANE/logs/$NAME.time"; REC="$LANE/receipts/$NAME.json"
export TMPDIR="$LANE/tmp" MALLOC_ARENA_MAX=2 PYTHONDONTWRITEBYTECODE=1 HOME="$LANE/tmp"
START="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
cd "$LANE/tmp"
/usr/bin/time -v -o "$TIMEF" timeout 140 taskset -c 0,1 \
  prlimit --cpu=120 --as=2147483648 -- python3 -I "$@" > "$LOG" 2>&1
RC=$?
END="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
RSS="$(grep 'Maximum resident' "$TIMEF" | awk '{print $NF}')"
UT="$(grep 'User time' "$TIMEF" | awk '{print $NF}')"
ST="$(grep 'System time' "$TIMEF" | awk '{print $NF}')"
WALL="$(grep 'Elapsed (wall' "$TIMEF" | awk '{print $NF}')"
SHA="$(sha256sum "$1" | cut -d' ' -f1)"
LOGSHA="$(sha256sum "$LOG" | cut -d' ' -f1)"
printf '{"name":"%s","script":"%s","script_sha256":"%s","args":"%s","start_utc":"%s","end_utc":"%s","exit_code":%s,"peak_rss_kib":%s,"user_s":%s,"sys_s":%s,"wall":"%s","log":"logs/%s.log","log_sha256":"%s","caps":"taskset 0,1; RLIMIT_CPU 120 s; timeout 140 s; RLIMIT_AS 2 GiB; MALLOC_ARENA_MAX=2; python3 -I"}\n' \
  "$NAME" "$1" "$SHA" "${*:2}" "$START" "$END" "$RC" "${RSS:-null}" "${UT:-null}" "${ST:-null}" "$WALL" "$NAME" "$LOGSHA" > "$REC"
cat "$REC"
