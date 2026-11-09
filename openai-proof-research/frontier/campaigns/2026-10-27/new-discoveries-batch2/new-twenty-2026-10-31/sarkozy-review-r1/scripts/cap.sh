#!/bin/bash
# capped single foreground run: CPU 120 s, wall 140 s, address space 1.5 GiB
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/sarkozy-review-r1
export TMPDIR=$L/tmp XDG_CACHE_HOME=$L/tmp/cache PYTHONDONTWRITEBYTECODE=1
cd $L/tmp
exec timeout 140 prlimit --cpu=120 --as=1610612736 /usr/bin/time -v python3 -I "$@"
