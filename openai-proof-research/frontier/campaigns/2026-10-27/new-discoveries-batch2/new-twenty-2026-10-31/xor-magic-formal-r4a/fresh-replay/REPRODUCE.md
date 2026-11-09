# Reproduction

Extract xor-magic-r4a-partial-source.zip into a new directory without any oleans. Set LEAN_BIN to the pinned Lean executable and LEAN_PACKAGES to the read-only pinned mathlib packages directory, then run `python3 -I replay.py` from the extracted directory.

Pinned toolchain: Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. Mathlib revision: d13f23b723b8a846827a245b89c10fc7d3f11612.

The driver refuses existing oleans, clears inherited environment configuration, checks source hashes, strictly rebuilds with -j1 -DwarningAsError=true, runs the three partitioned declaration audits and validates both lossless Expr DAGs, runs leanchecker on every module, and requires all twelve negative controls to fail with the expected kernel decide diagnostic. Each expensive child is guarded by tools/bounded.py: two CPUs, CPU 120 seconds, wall 140 seconds, sampled private RSS 6 GiB, address space 64 GiB and MALLOC_ARENA_MAX=2. Each child has an independent receipt and full log. Replay itself sequences bounded children; it is not a single expensive Lean call.

Audit and AuditR3 are unchanged. AuditR4a audits every declaration in the seven new modules, including generated declarations, using c.type and c.value? true, safety and partial flags and transitive allowed axioms. Audit modules are metaprograms implementing validation, not theorem dependencies. Proof-module declarations are the audited set.

This validates a partial proof packet and does not prove the missing endpoint. See GAPS.md and statement-correspondence.md.
