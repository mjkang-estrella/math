# Lean replay

Lean 4.34.1; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. The workspace package cache is read-only. Its formal/lake-manifest.json binds package revisions; no full upstream rebuild is claimed.

From the lane:

    python3 -I scripts/limited.py fresh-compile python3 -I scripts/replay.py compile
    python3 -I scripts/limited.py kernel-check python3 -I scripts/replay.py check
    python3 -I scripts/limited.py audit python3 -I scripts/lean.py lean/Audit.lean

Run sequentially, waiting for every previous process to exit. Compiler flags are -j2 -M3500 -DwarningAsError=true. The explicit kernel checker module is Interpolation. The wrapper limits affinity to two CPUs, CPU to 120 seconds, wall time to 140 seconds, and process-group sampled RSS to approximately 6 GiB; MALLOC_ARENA_MAX=2. All temporary paths are lane-local.

The zip is source-only: extract to a fresh empty directory, put its path and pinned dependency build/lib/lean paths on LEAN_PATH, compile Interpolation.lean to Interpolation.olean, then run leanchecker Interpolation with that path. Compile Audit.lean afterward. The stored fresh-replay directory and logs document the actual replay performed here.

Endpoint: OrientableTotalDomination.conjecture_true.
All 38 local/generated declarations are audited. Transitive axiom lists contain only propext, Classical.choice, Quot.sound. No independent review is claimed.
