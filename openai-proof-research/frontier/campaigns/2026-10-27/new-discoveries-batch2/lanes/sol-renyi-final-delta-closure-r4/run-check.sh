#!/bin/sh
set -eu
TASK_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
export PYTHONDONTWRITEBYTECODE=1
exec python "$TASK_DIR/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python "$TASK_DIR/check.py"
