#!/bin/bash
# run a command with 2 CPU, 2G memory, wall cap $1 seconds
W=$1; shift
exec systemd-run --user --scope --quiet -p MemoryMax=2G -p CPUQuota=200% timeout $W "$@"
