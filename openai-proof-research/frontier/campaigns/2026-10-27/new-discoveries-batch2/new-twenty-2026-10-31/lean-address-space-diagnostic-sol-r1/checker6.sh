#!/bin/bash
set -eu
export FORMAL_OPERATION=check
export FORMAL_MODULE="${1:?module name required}"
export FORMAL_ROOT="$(cd "$(dirname "$0")" && pwd)"
exec timeout 140 python3 -I -B "$FORMAL_ROOT/run_lean_6g.py" "${2:?unique receipt label required}" <<'PY'
import os,runpy
runpy.run_path(os.path.join(os.environ["FORMAL_ROOT"],"formal_command.py"),run_name="__main__")
PY
