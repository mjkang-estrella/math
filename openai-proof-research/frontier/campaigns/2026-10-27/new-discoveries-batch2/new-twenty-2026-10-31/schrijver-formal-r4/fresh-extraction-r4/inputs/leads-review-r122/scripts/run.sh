#!/bin/bash
set -eu
cd /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/leads-review-r122
export TMPDIR="$PWD/tmp" XDG_CACHE_HOME="$PWD/cache" PYTHONPYCACHEPREFIX="$PWD/cache" MALLOC_ARENA_MAX=2
ulimit -t 120
ulimit -v 6291456
exec taskset -c 0,1 timeout --kill-after=2s 140s "$@"
