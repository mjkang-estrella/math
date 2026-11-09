#!/bin/sh
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
G="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py"
for n in Literal Terminal Law Cells Product Prefix Marks Boards Injection Abundance Tail Concentration Assembly LastSplit SuffixUnion Growth Uniform UniformSuffix Observables FiniteProbability Measurability Median AllN Endpoint; do
 python3 "$G" python3 runner.py -o "$n.olean" "$n.lean" >/dev/null
done
python3 "$G" python3 runner.py --run StandaloneAudit.lean >/dev/null
