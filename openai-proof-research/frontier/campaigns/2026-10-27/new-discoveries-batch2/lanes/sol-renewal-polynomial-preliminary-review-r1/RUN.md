# Capped replay

Run each command with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1.

    python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-renewal-polynomial-preliminary-review-r1/check.py
    python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-renewal-polynomial-preliminary-review-r1/verify.py

The fixed guard enforces AS/groupRSS512MiB CPU210s wall230s. check.py requires installed SymPy, uses exact rational polynomial expansion and a bounded diagnostic grid. No Lean. Do not rerun freeze.py/access.py/finalize.py for verification: they are construction/retrieval records. verify.py is read-only except its receipt. To preserve final manifest identity, use verify.py directly on this completed lane; replaying check.py writes its deterministic result file.
