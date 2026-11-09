# Reproduce the partial r5p packet

Extract nut-r5p-source.zip into a new empty directory inside the assigned lane.
The packet contains sources and data, no oleans. Do not use the development
formal/ directory, which may already contain oleans.

Set LEAN_BIN to Lean 4.34.1, commit
5045d0056413266e57c625dcd7c365b10e377c52, and LEAN_PACKAGES to the read-only
mathlib package cache pinned at d13f23b723b8a846827a245b89c10fc7d3f11612.
Then run `python3 -I replay.py` from the extracted directory.

The driver rejects pre-existing oleans anywhere below its directory and
pre-existing replay logs. It sanitizes the environment, confines HOME and
TMPDIR to the extraction directory, uses MALLOC_ARENA_MAX=2, and builds the
ordered modules.json list using lean -j1 -DwarningAsError=true. Every Lean and
leanchecker invocation uses scripts/run_capped.py: at most 2 CPUs, CPU 120 s,
wall 140 s, sampled private RSS 6 GiB. Heavy invocations are sequential.

AuditAll emits each local declaration's module, complete type and value
(including opaque values), unsafe/partial/axiom flags and transitive axioms.
The audit rejects anything beyond propext, Classical.choice and Quot.sound.
The final audit has no new mathematical declarations of its own.
Negative-control logs and command/resource receipts are under logs/.
FinalEndpoint is conditional: Coverage8.lean is absent in this partial packet,
so logs/conditional-assembly.json records a skip. This is not a full endpoint
replay. A successful partial replay grants no solution credit.
