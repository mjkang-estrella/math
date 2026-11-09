# Guarded execution and verification

Every command after native instruction reads uses:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python SCRIPT

Original unchanged caps: AS512MiB, sampled process-group RSS512MiB, CPU210s, wall230s. No cap increased. Sampling cannot rule out unsampled transients. work/checks.py and work/middle.py are exact finite CAS exploration. work/proof_check.py is independent integer arithmetic. work/verify_final.py runs separately after final writes and repeats the integer proof checks, source/copied-input hashes, 1,589 immutable history-reference hashes, and complete manifest membership/digests. Manifest explicitly excludes itself and verification-receipt.json. Administrative snapshots are NOT bound to changing live ledger/NEXT files. No scientific inputs depend on live mutable administrative state.

The initial inventory-command exception is in FAILURES.md. No child/provider/Lean/browser/git/public/shared actions occurred.
