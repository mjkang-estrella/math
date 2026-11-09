#!/bin/bash
# Strict capped runner for crown-vnumber-formal-pi-r3.
# Usage: run.sh LABEL -- cmd args...
# Caps: CPU 120s (ulimit -t), wall 140s hard (kill+reap group, no grace overrun),
#       affinity = first 2 CPUs of caller's actual affinity mask,
#       AS 12GiB (ulimit -v), sampled group-RSS guard 6GiB, MALLOC_ARENA_MAX=2.
# Kills AND reaps the process group on timeout/guard. CPU is sampled live from
# the group (last sample before exit); recorded as sampled, never post-reap.
set -u
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
LABEL="$1"; shift
[ "${1:-}" = "--" ] && shift

MASK=$(taskset -pc $$ | sed 's/.*: //')
# expand mask, take first two cpu ids
read -r CA CB <<<"$(python3 - "$MASK" <<'PY'
import sys
out=[]
for part in sys.argv[1].split(','):
    if '-' in part:
        a,b=part.split('-'); out+= [str(i) for i in range(int(a),int(b)+1)]
    else: out.append(part)
print(out[0], (out[1] if len(out)>1 else out[0]))
PY
)"
AFF="$CA,$CB"

export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" MALLOC_ARENA_MAX=2
mkdir -p "$LANE/logs" "$LANE/receipt" "$LANE/tmp" "$LANE/cache" "$LANE/build"
STAMP=$(date +%s%N)
T0NS=$(date +%s%N)
LOG="$LANE/logs/${STAMP}_${LABEL}.log"
REC="$LANE/receipt/${STAMP}_${LABEL}.json"

{
  echo "CMD=$(printf '%q ' "$@")"
  echo "LABEL=$LABEL STAMP=$STAMP"
  echo "CAPS cpu_s=120 wall_s=140 affinity=$AFF mask=$MASK as_kib=12582912 rss_guard_kib=6291456 malloc_arena_max=2"
  echo "TMPDIR=$TMPDIR"
  echo "ENV LEAN_PATH=${LEAN_PATH:-<unset>}"
} >"$LOG"

PEAKF="$LANE/tmp/.peak_$STAMP"; CPUF="$LANE/tmp/.cpu_$STAMP"; GUARDF="$LANE/tmp/.guard_$STAMP"
echo 0 >"$PEAKF"; echo 0 >"$CPUF"; echo 0 >"$GUARDF"

( ulimit -t 120; ulimit -v 12582912
  exec setsid taskset -c "$AFF" env MALLOC_ARENA_MAX=2 TMPDIR="$TMPDIR" \
    XDG_CACHE_HOME="$XDG_CACHE_HOME" LEAN_PATH="${LEAN_PATH:-}" "$@"
) >>"$LOG" 2>&1 &
PID=$!

(
  while kill -0 "$PID" 2>/dev/null; do
    PG=$(ps -o pgid= -p "$PID" 2>/dev/null | tr -d ' '); [ -n "$PG" ] || break
    RSS=$(ps -eo pgid=,rss= 2>/dev/null | awk -v g="$PG" '$1==g{s+=$2} END{print s+0}')
    CPU=$(ps -eo pgid=,cputimes= 2>/dev/null | awk -v g="$PG" '$1==g{s+=$2} END{print s+0}')
    [ "$RSS" -gt "$(cat $PEAKF)" ] && echo "$RSS" >"$PEAKF"
    echo "$CPU" >"$CPUF"
    if [ "${RSS:-0}" -gt 6291456 ]; then
      echo "RSS_GUARD ${RSS}KiB; kill group $PG" >>"$LOG"; echo 1 >"$GUARDF"
      kill -KILL -- -"$PG" 2>/dev/null; break
    fi
    NOW=$(date +%s%N)
    if (( (NOW-T0NS)/1000000000 >= 140 )); then
      echo "WALL_CAP 140s; kill group $PG" >>"$LOG"; echo 2 >"$GUARDF"
      kill -KILL -- -"$PG" 2>/dev/null; break
    fi
    sleep 0.2
  done
) &
WATCH=$!

set +e; wait "$PID"; STATUS=$?
kill "$WATCH" 2>/dev/null; wait "$WATCH" 2>/dev/null
set -e
T1NS=$(date +%s%N)
PEAK=$(tail -1 "$PEAKF"); CPU=$(tail -1 "$CPUF"); GUARD=$(cat "$GUARDF")
rm -f "$PEAKF" "$CPUF" "$GUARDF"
WALLMS=$(( (T1NS-T0NS)/1000000 ))

{
  echo "EXIT=$STATUS"
  echo "WALL_MS=$WALLMS PEAK_GROUP_RSS_KIB_SAMPLED=$PEAK SAMPLED_GROUP_CPU_S=$CPU GUARD_FIRED=$GUARD"
} >>"$LOG"

python3 - "$REC" <<PY
import json
json.dump({
 "label": "$LABEL", "stamp": $STAMP, "exit": $STATUS, "wall_ms": $WALLMS,
 "sampled_group_cpu_s": $CPU,
 "peak_group_rss_kib_sampled": $PEAK, "rss_is_sampled_not_cgroup": True,
 "guard_fired": $GUARD, "cpu_cap_s": 120, "wall_cap_s": 140,
 "affinity_used": "$AFF", "affinity_mask_seen": "$MASK",
 "as_kib": 12582912, "rss_guard_kib": 6291456, "malloc_arena_max": 2,
 "log": "$LOG"}, open("$REC","w"), indent=1)
PY
echo "RECEIPT=$REC EXIT=$STATUS"
exit "$STATUS"
