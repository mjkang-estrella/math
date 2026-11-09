# Reproduce the partial certificate

This is a partial packet, not a refutation certificate. Read GAPS.md first.

Pinned Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. Read-only mathlib package cache pinned by the assignment to d13f23b723b8a846827a245b89c10fc7d3f11612. Dependencies are external, not vendored. The replay driver isolates LEAN_PATH and ignores inherited Lean/Lake settings.

Extract edgepattern-partial-source.zip into a NEW EMPTY DIRECTORY. Set LEAN_BIN to the absolute Lean binary and LEAN_PACKAGES to the directory containing the mathlib, batteries, aesop, Qq and other package caches. Run:

```sh
python3 -I scripts/replay.py
```

The driver refuses any existing .olean anywhere in the extraction; it never reuses a local build. Each module compiles with `-j1 -DwarningAsError=true`, then the adjacent leanchecker executable checks each proof module. Audit.lean enumerates every declaration in all proof modules, including generated names, with its module, full type, opaque body requested with value? true, flags and transitive axioms. It rejects unsafe/partial flags and axioms outside propext, Classical.choice and Quot.sound. Audit is a Lean metaprogram executed at compile time and adds no mathematical axioms.

Every Lean and leanchecker process runs through scripts/watchdog.py with two-CPU affinity, CPU 120 seconds, wall 140 seconds, sampled private RSS 6 GiB, and MALLOC_ARENA_MAX=2. Watchdog receipts report exit status, elapsed wall time and peak sampled private RSS. Only one heavy process runs at a time. CPU limits are enforced by the OS, wall/RSS by the parent monitor. Network fetches are unnecessary for replay.

Fresh replay logs and replay-receipt.json are retained under extracted/. Original development logs retain failed iterations without treating them as successful certificates. Negative controls run separately under negative-controls/.

Input hashes before copying are in inputs-before.json; after checks are in inputs-after.json. Every byte-for-byte copy identity is checked. No source input is modified.
