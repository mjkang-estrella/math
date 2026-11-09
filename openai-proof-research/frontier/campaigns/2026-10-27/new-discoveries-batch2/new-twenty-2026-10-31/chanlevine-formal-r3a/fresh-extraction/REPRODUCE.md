# Reproduce

Extract chanlevine-round3a-source.zip into a new empty directory inside this lane. Run python3 -I scripts/replay.py there; --resume reuses only receipts matching the complete source fingerprint. No lake update or network is used. All 19 modules compile strictly serially with Lean 4.34.1, -j1 -M3500 -DwarningAsError=true and receive leanchecker checks. The pinned read-only mathlib path and revision are the same as TASK.txt (d13f23b723b8a846827a245b89c10fc7d3f11612).

scripts/cap.py enforces CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, aggregate process-session RSS about 6 GiB; MALLOC_ARENA_MAX=2 and extraction-local TMPDIR/cache are set by replay.py. Every run has a unique retained log. No heavy calls run concurrently. Killed processes are waited on.

CountSpectralAudit.lean follows the reachable dependency closure seeded by every local declaration, including generated ones, in the CountSpectralControls import closure. The audit verifies no local forbidden flags, no unsafe/partial declarations in the closure, allowed axioms only, and exact set cardinality/uniqueness. Upstream extern/implemented_by metadata are inventoried separately and are allowed by the round-3a brief. This audit does not claim to audit unrelated compiler/tactic declarations outside the theorem/control dependency closure.

Five expected failures reject a wrong rotation sign, missing rotor determinant factor, treating conditional unitCount as unconditional, treating conditional spectralOrder as unconditional, and the wrong even-period parity coefficient. Small kernel-decided positive and negative controls are in CountSpectralControls. scripts/check.py uses exact integers and cyclotomic remainders for all 104 positive-level cases. It extends the inherited checker with the new coefficient-division recurrence versus the independent literal CycleTest DP.

The endpoint remains conditional on exactly TransferCountEvaluation and PrimitivePeriodData; replay success is not unconditional theorem success or acceptance.
