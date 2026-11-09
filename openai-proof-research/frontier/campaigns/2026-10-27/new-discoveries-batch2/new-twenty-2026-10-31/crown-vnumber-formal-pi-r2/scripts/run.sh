#!/bin/bash
# Strict capped runner for crown-vnumber-formal-pi-r2.
# Usage: run.sh LABEL -- cmd args...
# Caps: CPU 120s, wall 140s, affinity 2 CPUs, AS 12GiB, group-RSS guard 6GiB, MALLOC_ARENA_MAX=2.
# Kills and reaps the whole process group on guard failure or timeout.
# Receipt (JSON, machine) and log (text) are separate files.
set -u
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
LABEL="$1"; shift
[ "${1:-}" = "--" ] && shift
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" HOME="$HOME" MALLOC_ARENA_MAX=2
mkdir -p "$LANE/logs" "$LANE/receipt" "$LANE/tmp" "$LANE/cache"
STAMP=$(date +%s%N)
LOG="$LANE/logs/${STAMP}_${LABEL}.log"
REC="$LANE/receipt/${STAMP}_${LABEL}.json"

{
  echo "CMD=$(printf '%q ' "$@")"
  echo "LABEL=$LABEL STAMP=$STAMP"
  echo "CAPS cpu=120 wall=140 affinity=0,1 as_kib=12582912 rss_guard_kib=6291456 malloc_arena_max=2"
  echo "TMPDIR=$TMPDIR"
} >"$LOG"

# env for the receipt (no secrets; these are all paths/versions)
LEAN_PATH_VAL="${LEAN_PATH:-}"
{
  echo "ENV LEAN_PATH=$LEAN_PATH_VAL"
} >>"$LOG"

( ulimit -t 120; ulimit -v 12582912
  exec setsid taskset -c 0,1 env MALLOC_ARENA_MAX=2 TMPDIR="$TMPDIR" XDG_CACHE_HOME="$XDG_CACHE_HOME" \
    LEAN_PATH="$LEAN_PATH_VAL" timeout -k 5 140 "$@"
) >>"$LOG" 2>&1 &
PID=$!

PEAK=0
RSSGUARD=0
CPUFROMPS=0
(
  while kill -0 "$PID" 2>/dev/null; do
    PG=$(ps -o pgid= -p "$PID" 2>/dev/null | tr -d ' ')
    [ -n "$PG" ] || break
    RSS=$(ps -eo pgid=,rss= 2>/dev/null | awk -v g="$PG" '$1==g{s+=$2} END{print s+0}')
    if [ "$RSS" -gt "$PEAK" ]; then PEAK=$RSS; fi
    if [ "$RSS" -gt 6291456 ]; then
      echo "RSS_GUARD fired at ${RSS}KiB" >>"$LOG"
      kill -KILL -- -"$PG" 2>/dev/null
      echo "1" > "$LANE/tmp/.rssguard_${STAMP}"
      break
    fi
    sleep 0.2
  done
  echo "$PEAK" > "$LANE/tmp/.peak_${STAMP}"
) &
WATCH=$!

T0=$(date +%s%N)
set +e
wait "$PID"; STATUS=$?
T1=$(date +%s%N)
wait "$WATCH" 2>/dev/null
set -e
PEAK=$(cat "$LANE/tmp/.peak_${STAMP}" 2>/dev/null || echo 0)
RSSGUARD=$(cat "$LANE/tmp/.rssguard_${STAMP}" 2>/dev/null || echo 0)
rm -f "$LANE/tmp/.peak_${STAMP}" "$LANE/tmp/.rssguard_${STAMP}"
WALL_MS=$(( (T1 - T0) / 1000000 ))
CPU_S=$(ps -o cputimes= -p "$PID" 2>/dev/null || true)

{
  echo "EXIT=$STATUS"
  echo "WALL_MS=$WALL_MS PEAK_RSS_KIB=$PEAK RSS_GUARD=$RSSGUARD"
} >>"$LOG"

cat >"$REC" <<EOF
{
  "label": "$LABEL",
  "stamp": $STAMP,
  "cmd": $(printf '%s\n' "$@" | python3 -c 'import json,sys; print(json.dumps(sys.stdin.read().split()))'),
  "exit": $STATUS,
  "wall_ms": $WALL_MS,
  "peak_rss_kib": $PEAK,
  "rss_guard_fired": $RSSGUARD,
  "cpu_cap_s": 120,
  "wall_cap_s": 140,
  "affinity": "0,1",
  "as_kib": 12582912,
  "log": "$LOG"
}
EOF
echo "RECEIPT=$REC EXIT=$STATUS"
exit $STATUS
