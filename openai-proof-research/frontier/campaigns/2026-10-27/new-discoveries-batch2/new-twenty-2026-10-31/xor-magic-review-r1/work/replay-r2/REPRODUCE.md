# Replay of the partial r2 packet

This packet does not prove the universal corrected endpoint. It must not be credited as a solution.

Extract xor-magic-r2-partial-source.zip to a fresh directory. Set LEAN_BIN to the Lean 4.34.1 binary, commit 5045d0056413266e57c625dcd7c365b10e377c52. Set LEAN_PACKAGES to the pinned mathlib package directory (mathlib d13f23b723b8a846827a245b89c10fc7d3f11612). Run `python3 -I replay.py` from that directory.

The driver refuses any pre-existing olean, verifies source hashes, discards inherited environment configuration, and compiles each module with `-j1 -DwarningAsError=true`. It runs leanchecker on all modules and Audit, then six negative controls. It preserves logs and per-call resource receipts. Each build/check/control has two CPUs, 120 CPU seconds, 140 wall seconds, a sampled 6 GiB process-group private RSS guard, 64 GiB address space, and MALLOC_ARENA_MAX=2. No network is used. The portable driver requires Linux /proc, Python 3, and leanchecker beside LEAN_BIN.

Audit emits every local declaration name, source module, complete type AST, body via value? true, unsafe and partial flags, and transitive axioms. Kernel inductive, constructor and recursor declarations legitimately have no expression body and are explicitly identified. Definitions, theorems and opaque declarations must have bodies; local axioms are rejected. Only propext, Classical.choice and Quot.sound may occur transitively. Generated structure declarations are included. Audit itself only imports modules and runs a command, with no persistent proof declarations.

Negative controls change a finite degree, labelling and sum certificate, assert a false F4 identity, remove the n >= 2 restriction from the total-sum claim by testing n=1, and assert a fixed point in a seed matching. All must fail specifically because decide proves the stated proposition false. A second invocation must refuse the existing oleans.

The original Literal.lean, Certificates.lean, 32 Base*.lean modules and BaseEndpoints.lean are byte-identical to r1. Their copied audit has been extended to the additional r2 modules. Source input hashes and copy identities are in receipts/. No hash of an ordinary proof or JSON certificate is treated as a Lean proof.
