# Execution record

All helper commands after the documented initial orientation violation used:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py <command>

The unmodified guard enforces AS/RSS 512 MiB, CPU 210s, wall 230s. No cap increase. Native bounded instruction reads and apply_patch used the explicit exception. No children, git operations, shared edits, browser, external messages/posts/uploads, MathDB changes, Lean or manuscript work.

Independent checker completed with guard_exit 0, reason null, sampled process-group peak RSS 11,894,784 bytes, wall 0.401146429 seconds. Retrieval helper completed with guard_exit 0, reason null, sampled peak RSS 25,706,496 bytes, wall 4.316832926 seconds. Exact counts and UTC are in check-results.json. These sampled figures do not exclude sub-sampling transients.

Finalization: generate manifest.json after all other artifact writes, explicitly excluding manifest.json and verification-receipt.json. Then run verify_final.py in a separate guarded invocation. The separate receipt checks manifest inventory and hashes, scientific original/copy bindings and administrative snapshot-copy integrity. It does not bind mutable live NEXT/ledger/context originals. No writes after verification except the excluded receipt produced by that invocation.
