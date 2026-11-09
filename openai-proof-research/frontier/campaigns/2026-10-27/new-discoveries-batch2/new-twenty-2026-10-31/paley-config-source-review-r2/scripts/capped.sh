#!/bin/bash
# Run a command capped at 2 CPUs, 6 GiB RSS, CPU 120 s, wall 140 s.
exec systemd-run --user --scope --quiet -p MemoryMax=6G -p CPUQuota=200% bash -c 'ulimit -t 120; exec timeout 140 "$@"' _ "$@"
