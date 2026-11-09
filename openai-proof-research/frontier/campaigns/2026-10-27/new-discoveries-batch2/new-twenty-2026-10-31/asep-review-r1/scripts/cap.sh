#!/bin/bash
# usage: cap.sh LOG.json cmd...   -- systemd user scope MemoryMax=6G + reviewer watchdog (2 CPUs, CPU 120 s, wall 140 s)
LOG=$1; shift
exec systemd-run --user --scope --quiet -p MemoryMax=6G -p MemorySwapMax=0 -p CPUQuota=200% \
  timeout -s KILL 150 python3 -I -B "$(dirname "$0")/watch.py" "$LOG" -- "$@"
