#!/bin/bash
set -u
LANE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r154
export TMPDIR="$LANE/tmp" TMP="$LANE/tmp" TEMP="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONPYCACHEPREFIX="$LANE/cache/pycache" MALLOC_ARENA_MAX=2
CPUS=$(awk '/Cpus_allowed_list/{print $2}' /proc/self/status | awk -F '[-,]' '{print $1","$1+1}')
setsid timeout -k 2 140 taskset -c "$CPUS" bash -c 'ulimit -t 120; exec "$@"' bash "$@" &
p=$!
while kill -0 "$p" 2>/dev/null; do
 rss=$(ps -eo pgid=,rss= | awk -v p="$p" '$1==p{s+=$2}END{print s+0}')
 if [ "$rss" -gt 6291456 ]; then echo "RSS watchdog killed $p at $rss KiB" >&2; kill -KILL -- -"$p" 2>/dev/null; fi
 sleep 0.25
done
wait "$p"
