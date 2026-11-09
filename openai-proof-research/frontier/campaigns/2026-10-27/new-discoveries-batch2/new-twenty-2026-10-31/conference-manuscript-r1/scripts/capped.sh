#!/bin/bash
# Capped runner for every computation in this lane.
#   scripts/capped.sh TAG command [args...]
# Caps: CPUs 0,1 (taskset); RLIMIT_CPU 120 s; wall 140 s (timeout -k 2);
# RLIMIT_AS 2 GiB (so RSS < 2 GiB); MALLOC_ARENA_MAX=2; lane-local TMPDIR.
# Writes receipts/calls/TAG.{stdout,stderr,time,json}.  One call at a time.
L=$(cd "$(dirname "$0")/.." && pwd)
tag=$1; shift
R="$L/receipts/calls"
start=$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)
( ulimit -t 120; ulimit -v 2097152
  export MALLOC_ARENA_MAX=2 TMPDIR="$L/tmp" TMP="$L/tmp" TEMP="$L/tmp" XDG_CACHE_HOME="$L/tmp/xdg"
  cd "$L" && exec timeout -k 2 140 taskset -c 0,1 /usr/bin/time -v -o "$R/$tag.time" "$@" ) \
  > "$R/$tag.stdout" 2> "$R/$tag.stderr"
rc=$?
end=$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)
rss=$(grep 'Maximum resident' "$R/$tag.time" 2>/dev/null | awk '{print $6}')
cpu_u=$(grep 'User time' "$R/$tag.time" 2>/dev/null | awk '{print $4}')
cpu_s=$(grep 'System time' "$R/$tag.time" 2>/dev/null | awk '{print $4}')
wall=$(grep 'Elapsed (wall' "$R/$tag.time" 2>/dev/null | awk '{print $NF}')
printf '{"tag":"%s","command":"%s","rc":%d,"utc_start":"%s","utc_end":"%s","max_rss_kb":"%s","user_s":"%s","sys_s":"%s","wall":"%s","caps":{"cpus":"0,1","rlimit_cpu_s":120,"wall_s":140,"rlimit_as_kib":2097152,"MALLOC_ARENA_MAX":"2"}}\n' \
  "$tag" "$(echo "$*" | sed 's/"/\\"/g')" "$rc" "$start" "$end" "$rss" "$cpu_u" "$cpu_s" "$wall" > "$R/$tag.json"
echo "$tag rc=$rc maxrss_kb=$rss user=$cpu_u wall=$wall"
exit $rc
