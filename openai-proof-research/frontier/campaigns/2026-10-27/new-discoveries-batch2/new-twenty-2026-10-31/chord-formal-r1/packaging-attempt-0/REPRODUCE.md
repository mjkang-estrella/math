# Reproduction

Use Lean 4.34.1 at /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin. The read-only mathlib package directory is /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, designated pin d13f23b723b8a846827a245b89c10fc7d3f11612. This lane does not use git and does not mutate or fetch packages.

Run `scripts/rebuild.sh` from an extraction under this lane. It serially compiles each dependency using -j1 -M3500 -DwarningAsError=true, and runs leanchecker with an explicit module name for every compiled module. Successful module hashes are recorded for resumption. A fresh extraction starts with no build products or success markers. If editing a dependency during a resumed build, delete later success markers too; the supplied replay is for immutable source archives.

Every Lean, leanchecker and Python invocation must use scripts/capped.sh. This sets TMPDIR and XDG_CACHE_HOME within its root, MALLOC_ARENA_MAX=2, a two-CPU affinity (0,1), CPU 120 s and wall 140 s. A process-group RSS watchdog samples summed RSS every 0.1 s and kills the group beyond 6 GiB. Unique full logs retain peak sampled RSS. Do not run more than one heavy process at a time.

Run `scripts/capped.sh python3 -I scripts/regression.py` for independent finite regression and numerical negative controls. The script reimplements both models, checks Euler parity and nonnegativity before division, and enumerates every matching through five chords. These Python results are not formal enumeration proofs.

The audit imports all declarations from the endpoint import closure, including generated/private declarations. It uses allowOpaque := true, checks exact inventory/audited set equality, and rejects LOCAL axiom declarations, unsafe/partial flags, _unsafe_rec companions, implemented_by, extern, and unapproved transitive axioms. Upstream metadata is separately reported; runtime implementations in Lean/mathlib are not falsely classified as newly added lane declarations.

The historical finite4.py / split4.py / optimize4.py / chunk4.py scripts record development steps and are not replay entrypoints. Use the checked-in Lean files as archive sources. Only rebuild.sh and regression.py are needed for validation.
