#!/bin/bash
set -eu
LANE="$(cd "$(dirname "$0")/.." && pwd)"
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/tmp" PYTHONPYCACHEPREFIX="$LANE/tmp/pycache" MALLOC_ARENA_MAX=2
ulimit -t 120
ulimit -c 0
exec perl "$LANE/scripts/watch.pl" taskset -c 30,31 timeout -k 2 140 "$@"
