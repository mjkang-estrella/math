# Bounded replay

Every Python, retrieval, extraction and hash operation in this lane used the assigned immutable helper guard, with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1. Fixed limits: AS512MiB; sampled process-group RSS512MiB; CPU210s; wall230s. No cap raises. RSS sampling cannot rule out unsampled transient spikes. Native bounded reads and apply_patch were used as authorized.

From repository root, define shell variables for the absolute paths:

    lane=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-wide-independent-scout-r249
    guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$guard" python "$lane/checks.py"
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$guard" python "$lane/finalize.py"
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$guard" python "$lane/verify.py"

checks.py recreates deterministic diagnostic output. Finalize must precede the separate verify invocation. Do not rerun retrieval scripts to retry parked inaccessible routes. The manifest and verification receipt exclude themselves from manifest entries; every other lane file is included. No recursive history copying.
