#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
cpus=$(python -c 'import os;print(",".join(map(str,sorted(os.sched_getaffinity(0))[:2])))')
timeout 140s taskset -c "$cpus" python diagnostics.py > diagnostics-reproduction.log 2>&1
timeout 140s taskset -c "$cpus" python sustained.py > sustained-reproduction.log 2>&1
timeout 140s taskset -c "$cpus" python verify.py > verification-reproduction.log 2>&1
