#!/bin/bash
R=$(cd "$(dirname "$0")/.." && pwd)
B=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
LP="$R/build"; for p in $PKG/*; do LP="$LP:$p/.lake/build/lib/lean"; done
run(){ tag=$1; shift; ( ulimit -t 120; PATH=$B:$PATH MALLOC_ARENA_MAX=2 TMPDIR=$R/tmp LEAN_PATH=$LP timeout -k 2 140 taskset -c 0,1 /usr/bin/time -v "$@" ) > $R/logs/$tag.log 2>&1; rc=$?; echo "$tag rc=$rc maxrss_kb=$(grep 'Maximum resident' $R/logs/$tag.log | awk '{print $6}')"; return $rc; }
cd $R/replay/packet
for m in Base C0R0 C0R1 C0R2 C0R3 C0R4 C0R5 C0R6 C0R7 C1R0 C1R1 C1R2 C1R3 C1R4 C1R5 C1R6 C1R7 Certificates Final Semantics Audit; do
  run build-$m $B/lean -j1 -M3500 -DwarningAsError=true -o $R/build/$m.olean $m.lean || exit 1
  run checker-$m $B/leanchecker $m || exit 1
done
run root-meta $B/lean -j1 -M3500 -DwarningAsError=true $R/rootcheck/RootMeta.lean || exit 1
echo ROOT_REPLAY_DONE
