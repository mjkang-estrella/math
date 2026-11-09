# Reproduction

Extract wheel-complete-source.zip into a fresh empty directory. The driver refuses any existing .olean file beneath the extraction.

Set LEAN_BIN to the pinned Lean 4.34.1 binary (commit 5045d0056413266e57c625dcd7c365b10e377c52) and LEAN_PACKAGES to the read-only pinned mathlib package-cache directory (mathlib d13f23b723b8a846827a245b89c10fc7d3f11612). Run `python3 -I replay.py` from the extraction. No network is required. The driver checks source SHA-256 hashes, sanitizes the Lean environment, builds every module using `-j1 -DwarningAsError=true`, audits every local declaration, runs leanchecker for every module, and runs negative controls. Each expensive subprocess is guarded with at most 2 CPUs, CPU 120 seconds, wall 140 seconds, 6 GiB sampled private RSS and 64 GiB address space. MALLOC_ARENA_MAX is 2.

The packet is a complete source-only formal certificate. Lane-level input hashes, source correspondence, results and replay receipts accompany it. Acceptance is exclusively root's responsibility.
