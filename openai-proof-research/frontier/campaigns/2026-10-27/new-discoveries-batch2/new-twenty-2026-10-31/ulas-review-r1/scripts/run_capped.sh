#!/usr/bin/env bash
# Usage: scripts/run_capped.sh <logname> <python-script> [args...]
# One capped python3 -I process: 2 CPUs (taskset 0,1), CPU 120 s, wall 140 s,
# address space 6 GiB, MALLOC_ARENA_MAX=2, TMPDIR lane-local. Full stdout/stderr logged.
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"
name="$1"; shift
export MALLOC_ARENA_MAX=2 TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/tmp/cache" PYTHONDONTWRITEBYTECODE=1
log="$LANE/logs/$name.log"
start=$(date -u +%FT%TZ)
( ulimit -t 120; ulimit -v 6291456; exec taskset -c 0,1 timeout 140 /usr/bin/time -v python3 -I "$@" ) >"$log" 2>"$LANE/logs/$name.stderr"
rc=$?
end=$(date -u +%FT%TZ)
python3 -I - "$LANE/logs/$name.receipt.json" "$name" "$start" "$end" "$rc" "$log" "$@" <<'PY'
import sys, json, hashlib
out, name, s, e, rc, log, *cmd = sys.argv[1:]
h = lambda p: hashlib.sha256(open(p,'rb').read()).hexdigest()
d = dict(name=name, start_utc=s, end_utc=e, exit_code=int(rc), command=["python3","-I"]+cmd,
         log=log, log_sha256=h(log), stderr_sha256=h(log[:-4]+".stderr"),
         script_sha256=h(cmd[0]),
         caps=dict(cpus="taskset 0,1", cpu_seconds=120, wall_seconds=140, address_space_kib=6291456, MALLOC_ARENA_MAX=2))
json.dump(d, open(out,'w'), indent=1)
PY
echo "rc=$rc log=$log"; tail -n 5 "$LANE/logs/$name.stderr" | head -3; grep -E "Maximum resident|Elapsed|User time" "$LANE/logs/$name.stderr"
