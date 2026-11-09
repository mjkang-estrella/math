# Partial formalization replay

This packet does not prove the corrected theorem for every n ≥ 4. It has zero qualifying credit. Read SUMMARY.md and statement-correspondence.md before using it.

Extract the source-only zip to a new directory. Set LEAN_BIN to the Lean executable and LEAN_PACKAGES to the pinned mathlib package directory, then run:

```
LEAN_BIN=/path/to/lean-4.34.1/bin/lean LEAN_PACKAGES=/path/to/.lake/packages python3 -I replay.py
```

The required Lean commit is 5045d0056413266e57c625dcd7c365b10e377c52. The assigned mathlib revision is d13f23b723b8a846827a245b89c10fc7d3f11612. External cached dependencies are trusted inputs, not distributed in the packet. The driver checks the Lean version and source hashes; it does not independently establish the revision of a supplied package cache.

The driver refuses any existing olean, overwrites inherited Lean paths with the packet source directory and supplied package libraries, uses an empty local home/temp directory, and compiles each module with lean -j1 -DwarningAsError=true. Each expensive process has two CPU affinity slots, CPU 120 seconds, wall 140 seconds, a 64 GiB address-space limit and a sampled 6 GiB private RSS guard (including its process group). MALLOC_ARENA_MAX=2 is set. Full logs and per-call receipts go into logs/.

Every proof declaration, including compiler-generated auxiliary declarations, in every module listed in modules.json is audited: module, complete type and body AST using value? true, unsafe and partial flags, and transitive axioms. Only propext, Classical.choice and Quot.sound are allowed. Audit.lean is the trusted inspection program rather than an endpoint module. leanchecker separately replays each listed module and Audit. It checks local declarations against trusted imports; it is not an external kernel or a fresh replay of all mathlib declarations.

Negative controls attempt to prove a false regular degree, a constant bijective labelling, and a false open-neighborhood sum on the closed degree-4 certificate. The driver requires each to fail specifically because decide evaluates to false. These controls test those three properties only.

No native computation oracle is used. Adjacency bitmasks describe graphs on Fin 16 and Fin 32. Symmetry, absence of loops, degrees, bit-label bijections and actual ZMod-valued neighborhood sums are proved by kernel decide. The numerical encoding is bridged by binaryLabel and the kernel-proved label_bijective declarations, not by assuming that a Python XOR checker is sound. Connectivity follows from a proved parent/rank descent lemma and kernel-checked parent certificates.
