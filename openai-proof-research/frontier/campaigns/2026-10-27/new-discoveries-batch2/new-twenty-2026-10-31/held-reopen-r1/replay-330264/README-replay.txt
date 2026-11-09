This packet is self-contained in its local Lean sources; external imports use the pinned installed toolchain and read-only mathlib package cache.
Lean 4.34.1: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612
Packages: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages

From a fresh extraction run: python3 replay.py
It verifies the packet manifest and compiles every local module in dependency order.
No bundled oleans are used. It uses at most two CPUs, Lean -j2 -M3500,
warningAsError=true, and a per-module wall limit of 300 seconds.
Expected slow module: SpectralWitness (the preserved r2 spectral certificates).
The mathematical entry point is MathDB330264.conjecture_false in Endpoint.lean.
The final endpoint and other declaration axiom audits must contain only
propext, Classical.choice, Quot.sound. The receipt is replay-receipt.json.

The generator is optional: generated ConcreteMachine.lean already contains every
finite certificate. generate_machine.py reads the frozen r2 edge lists at the
neighboring original workspace location; regeneration is not needed for replay.

This is a full Lean endpoint, not an acceptance/novelty certificate. No campaign
count changes are made. Source fidelity and novelty/significance require the
independent reviews assigned by the root.
