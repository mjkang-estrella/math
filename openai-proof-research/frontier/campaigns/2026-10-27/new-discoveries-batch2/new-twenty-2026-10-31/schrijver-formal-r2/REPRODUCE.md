# Reproduction

Use Lean 4.34.1 and the pinned read-only mathlib cache specified in TASK.txt. Extract the source-only zip to a fresh empty directory. Run python3 -I scripts/replay.py there. The script strictly builds and leanchecks every module in outputs/modules.json in serial order under scripts/run_capped.py, and runs negative controls. Use --resume only with the identical SOURCE-MANIFEST.json packet; successful receipts permit resumption. Each process has CPU 120 s, wall 140 s, two CPU affinity, sampled private RSS 6 GiB, MALLOC_ARENA_MAX=2, Lean -j1 -M3500 and warningAsError=true. No compiled objects are shipped in the source archive.

The packet is partial. PASS_PARTIAL_ONLY means all shipped modules checked, not that the literal endpoint was proved. Inspect SUMMARY.md and results.json for outstanding obligations. Fresh-extraction logs contain the declaration audit and per-process receipts.
