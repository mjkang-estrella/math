# Reproduction

Extract edgepattern-r3-partial-source.zip into a new empty directory, set LEAN_BIN to the Lean 4.34.1 executable and LEAN_PACKAGES to the read-only pinned .lake/packages directory, and run `python3 -I scripts/replay.py`.

The driver refuses existing .olean files, ignores inherited LEAN/LAKE variables, isolates HOME and TMPDIR within the extraction and rebuilds every module in scripts/modules.json with `-j1 -DwarningAsError=true`. It then invokes leanchecker on every module. The pinned Lean commit is 5045d0056413266e57c625dcd7c365b10e377c52; mathlib is d13f23b723b8a846827a245b89c10fc7d3f11612.

Every Lean or leanchecker invocation, including --version, uses scripts/watchdog.py: at most two CPUs, CPU 120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2. The RSS watchdog now triggers at 5.75 GiB to leave sampling headroom below the assigned 6 GiB cap. A monolithic development evaluation was killed at the original 6 GiB threshold after a sampled jump to 7.38 GB; it is not a passing verification. All final evaluation certificates use blocks of at most 256 masks.

AuditR3 uses the complete shared expression encoding documented in AUDIT-FORMAT.md and logs all local declarations, including generated declarations, full types and opaque bodies, unsafe/partial flags, and transitive axioms. It rejects any axiom outside propext, Classical.choice and Quot.sound. Audit and AuditR2 remain byte-identical. Negative controls can be run in the lane with `python3 -I scripts/negative.py` after the extracted replay; they include incorrect mask, total and canonical expectation claims and existing-object refusal.

This is a partial certificate: the universal classification and unconditional conjecture endpoint remain absent. See GAPS.md.

Early development checks reused the dev-MaskR3.log and dev-TreeModelsR3.log filenames, so those files retain only the last such invocation. The development runner was changed to unique timestamped logs afterward. Final replay and negative-control logs are complete and separate from those development files.

An early MaskR3 development invocation was launched before the inherited-module development batch's session had been drained; overlap at that tail was not ruled out. Early development is therefore not certified to meet the one-heavy-process rule. The final replay driver waits for every watchdog invocation before starting the next, as does the negative-control driver. Treat only final verification receipts as the sequential verification evidence.

The initial flat AuditR3 print exceeded the 120-second CPU cap after 294 declarations. The final audit records complete type/body expression DAGs instead, including all constructor fields, names, levels, binders and metadata. Its development check covered 1,463 declarations and 222,524 nodes without elisions.
