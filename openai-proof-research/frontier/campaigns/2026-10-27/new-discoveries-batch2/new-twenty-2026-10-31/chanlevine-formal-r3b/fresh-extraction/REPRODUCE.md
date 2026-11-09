# Reproduction

Extract chanlevine-round3b-source.zip into a new empty directory inside this lane. Run `python3 -I scripts/replay.py --resume` there. This compiles all 18 modules in dependency order with Lean 4.34.1, `-j1 -M3500 -DwarningAsError=true`, and runs leanchecker on each one. Fingerprinted receipts allow strict replay to resume only for identical sources.

Pinned read-only mathlib packages: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`, revision d13f23b723b8a846827a245b89c10fc7d3f11612. Lean binary: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`.

Each heavy process runs serially through scripts/cap.py with CPUs 0 and 1, CPU 120 seconds, wall 140 seconds and process-group RSS about 6 GiB. MALLOC_ARENA_MAX=2; TMPDIR, build and cache directories are extraction-local. Logs have unique names. The archive contains source and documentation only, no compiled artifacts.

Sem3Audit inspects every local declaration in the SemFinal2 import closure and recursively visits complete type/body dependencies with allowOpaque := true and inductive constructors. Replay recomputes closure equality, rejects local executable overrides and all unsafe or partial dependencies, and records allowed upstream extern/implemented_by entries separately. The proof audit covers the dependency closure, not the entire imported compiler/tactic environment.

Negative controls deliberately fail compilation for an incorrect weight, an empty Hamiltonian test, missing vertex coverage and omission of the remaining CycleTestWord premise. The reviewer SCC script checks 18 cases with n = 3 through 8, m = 1 through 3.

Final theorems are in namespace ChanLevine.Sem3. AmbientBridge and three residual Props are unconditional. CycleTestBridge still assumes CycleTestWord; ConnectedFibres still assumes RecurrentNormalization. Root decides acceptance.
