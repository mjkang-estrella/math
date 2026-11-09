#!/bin/bash
# Capped selftest: <=2 CPU affinity, 30s wall guard, MALLOC_ARENA_MAX=2
cd "$(dirname "$0")"
export MALLOC_ARENA_MAX=2
taskset -c 0,1 timeout -k 5 30 python3 scripts/search.py --selftest
echo "exit=$?"
