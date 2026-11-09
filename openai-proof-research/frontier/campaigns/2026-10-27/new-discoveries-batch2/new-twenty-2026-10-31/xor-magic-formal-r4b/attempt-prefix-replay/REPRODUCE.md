# Reproduction

Use Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, and the read-only mathlib package cache pinned to d13f23b723b8a846827a245b89c10fc7d3f11612.

Extract xor-magic-r4b-source.zip into a new directory, with no existing oleans anywhere below it. Set LEAN_BIN to the absolute Lean executable and LEAN_PACKAGES to the absolute package-cache directory. Run `python3 -I replay.py` from the extraction directory. The driver sanitizes its environment, checks source hashes and toolchain, strictly rebuilds each module, runs the two inherited audits and the r4b audit, verifies both lossless expression DAGs, runs leanchecker on every module, and checks twelve failing negative controls. It refuses any preexisting olean.

Every Lean, leanchecker and DAG-check call uses tools/bounded.py: two CPUs, 120 CPU seconds, 140 wall seconds, 6 GiB sampled private RSS, 64 GiB address space, MALLOC_ARENA_MAX=2. All subprocess output and resource receipts are retained in logs/. The driver creates its temporary and home directories only inside the extraction directory. It does not download dependencies or invoke git.

The receipt logs/replay-receipt.json marks validation of this packet, not root acceptance or a universal MathDB solution. The input hash manifest receipts/inputs-before.json binds the designated immutable sources and their local copies; receipts/inputs-after.json verifies their preservation.
