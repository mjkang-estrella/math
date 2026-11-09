# Reproduce the partial packet

Use Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and the read-only
mathlib package cache pinned d13f23b723b8a846827a245b89c10fc7d3f11612. No package
installation or network access is needed for replay. The cache includes all
transitive package oleans; these are trusted pinned dependencies, not rebuilt.

Extract nut-partial-source.zip into a NEW empty directory inside this lane.
The portable driver refuses ANY existing .olean under its extraction root.
Run with the absolute executable and package paths in the two environment variables:

```
LEAN_BIN=/path/to/lean LEAN_PACKAGES=/path/to/packages python3 -I replay.py
```

The sibling leanchecker executable is required. The driver sanitizes its child
environment, sets its own HOME/TMPDIR within the extraction, and compiles with
`-j1 -DwarningAsError=true`. Each build and leanchecker invocation gets a
process-group watchdog, at most 2 CPUs, 120 CPU seconds, 140 wall seconds,
6 GiB sampled aggregate private RSS and MALLOC_ARENA_MAX=2. One heavy job runs
at a time. Logs and JSON receipts are retained. Every module is separately
checked by leanchecker. Audit enumerates every declaration by defining module,
including generated names, prints full types, opaque-inclusive bodies,
unsafe/partial/axiom flags and transitive axioms. Only propext, Classical.choice
and Quot.sound are allowed. Negative controls must fail without hitting caps.

The expected result is PASS PARTIAL PACKET ONLY. This is NOT a replay of a
proof of the conjecture; see GAPS.md. Inputs and mathematical evidence are
retained separately in this lane and are not executable dependencies of the
small source-only packet. No original or prebuilt local olean is packaged.
