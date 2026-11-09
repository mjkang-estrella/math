#!/bin/bash
# resumable: skips modules whose build and checker both succeeded earlier
R=$(cd "$(dirname "$0")/.." && pwd)
B=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
LP="$R/build"; for p in $PKG/*; do LP="$LP:$p/.lake/build/lib/lean"; done
run(){ tag=$1; shift; ( ulimit -t 120; PATH=$B:$PATH MALLOC_ARENA_MAX=2 TMPDIR=$R/tmp LEAN_PATH=$LP timeout -k 2 140 taskset -c 0,1 /usr/bin/time -v "$@" ) > $R/logs/$tag.log 2>&1; rc=$?; echo "$tag rc=$rc maxrss_kb=$(grep 'Maximum resident' $R/logs/$tag.log | awk '{print $6}') wall=$(grep 'Elapsed (wall' $R/logs/$tag.log | awk '{print $NF}')"; return $rc; }
cd $R/replay/packet
START=$(date +%s); BUDGET=${BUDGET:-480}
for m in $(cat $R/rootcheck/order.txt); do
  [ -f $R/build/$m.ok ] && continue
  [ $(( $(date +%s) - START )) -gt $BUDGET ] && { echo "CHUNK_BUDGET_REACHED"; exit 3; }
  run build-$m $B/lean -j1 -M3500 -DwarningAsError=true -o $R/build/$m.olean $m.lean || exit 1
  run checker-$m $B/leanchecker $m || exit 1
  touch $R/build/$m.ok
done
run root-meta $B/lean -j1 -M3500 -DwarningAsError=true $R/rootcheck/RootMeta.lean || exit 1
echo ROOT_REPLAY_DONE
