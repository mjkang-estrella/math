# Replay the partial packet

Extract xor-magic-r3-partial-source.zip into a new empty directory. Set LEAN_BIN to the Lean 4.34.1 binary at commit 5045d0056413266e57c625dcd7c365b10e377c52. Set LEAN_PACKAGES to the pinned mathlib packages directory (mathlib d13f23b723b8a846827a245b89c10fc7d3f11612). Run `python3 -I replay.py` in the extraction.

The driver refuses existing oleans, checks source hashes, clears inherited Lean and user configuration, rebuilds with `-j1 -DwarningAsError=true`, runs leanchecker, audits all local declarations including generated structure declarations (Audit covers inherited modules; AuditR3 covers the eight new proof modules), and checks nine failing negative controls. Each Lean or leanchecker call uses tools/bounded.py: two CPUs, 120 seconds CPU, 140 seconds wall, 6 GiB sampled private RSS, 64 GiB address space, MALLOC_ARENA_MAX=2. Logs and per-call receipts are created inside the extraction. Only propext, Classical.choice and Quot.sound are permitted by the declaration audit.

This verifies only the partial theorem set. The universal corrected endpoint is absent. Consult GAPS.md before reuse. The packet contains sources only; the development oleans in the lane are not delivered in it.
