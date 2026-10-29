#!/bin/sh
set -eu
task_lane_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python "$task_lane_dir/helper_guard.py" python "$task_lane_dir/check.py"
