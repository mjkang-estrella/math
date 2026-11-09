#!/bin/bash
set -euo pipefail
LANE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONPYCACHEPREFIX="$LANE/cache/python" MALLOC_ARENA_MAX=2
ulimit -t 120
exec python3 -I "$LANE/scripts/run_capped.py" "$LANE/logs/run-$(date +%s%N).log" "$@"
