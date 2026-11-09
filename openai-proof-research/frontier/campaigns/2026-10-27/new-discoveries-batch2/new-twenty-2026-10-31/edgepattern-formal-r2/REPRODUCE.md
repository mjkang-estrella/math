# Replay

Extract edgepattern-r2-partial-source.zip into a new empty directory. Set:

```sh
export LEAN_BIN=/path/to/lean-4.34.1-linux/bin/lean
export LEAN_PACKAGES=/path/to/pinned/.lake/packages
python3 -I scripts/replay.py
```

Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and the supplied mathlib cache at revision d13f23b723b8a846827a245b89c10fc7d3f11612 are required. The script ignores inherited LEAN/LAKE paths, isolates HOME and TMPDIR inside the extraction, refuses any existing .olean, and rebuilds all eleven local modules with -j1 -DwarningAsError=true. It then runs leanchecker on all eleven modules. Every invocation, including version and leanchecker, goes through the sampled-private-RSS watchdog: 6 GiB, 120 CPU seconds, 140 wall seconds, two-CPU affinity, MALLOC_ARENA_MAX=2. Processes run sequentially.

The audit records module, full type, opaque body, unsafe/partial flags and transitive axioms for every declaration in all eleven local modules, including generated declarations encountered in their environments. Only propext, Classical.choice and Quot.sound are permitted. Audit.lean is the unchanged r1 audit; AuditR2.lean covers the full continuation.

The recorded negative controls were run by scripts/negative.py in the lane, using its fresh extracted/formal objects. They test false expectation, false girth, false independence and existing-object refusal. They intentionally do not compile as positive proof sources and are excluded from the replay module list.

This is a partial certificate. See GAPS.md. No unconditional refutation is asserted.
