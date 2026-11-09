#!/bin/bash
# Reviewer strict replay. Each step via limited.py (2 CPUs, CPU 120 s, wall 140 s, private RSS 6 GiB).
set -e
L=$(cd "$(dirname "$0")/.." && pwd); F=$L/fresh
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
CACHE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
LP=$F; for d in $CACHE/*/; do LP=$LP:${d%/}/.lake/build/lib/lean; done
export LEAN_PATH=$LP LEAN_NUM_THREADS=1 MALLOC_ARENA_MAX=2 PATH=$BIN:/usr/bin:/bin
cd $F
# forbidden-token scan (comments stripped)
python3 -I - "$F/CaterpillarCenter.lean" "$F/OrdinalLine.lean" <<'PY'
import re,sys
for p in sys.argv[1:]:
    t=open(p).read(); b=re.sub(r'/-.*?-/','',t,flags=re.S); b=re.sub(r'--.*','',b)
    bad=re.findall(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern|opaque|macro_rules|elab|run_cmd|run_tac|set_option|debug\.skipKernelTC)\b',b)
    print(p.rsplit('/',1)[1],'forbidden tokens:',bad); assert not bad
PY
for M in CaterpillarCenter OrdinalLine; do
  python3 $L/scripts/limited.py build-$M $BIN/lean -j1 -DwarningAsError=true -o $F/$M.olean -i $F/$M.ilean $F/$M.lean
  test ! -s $L/logs/build-$M.log
  python3 $L/scripts/limited.py leanchecker-$M $BIN/leanchecker $M
  python3 $L/scripts/limited.py audit-$M $BIN/lean -j1 -DwarningAsError=true $F/RevAudit$M.lean
done
python3 $L/scripts/limited.py statements $BIN/lean -j1 $F/RevStatements.lean
