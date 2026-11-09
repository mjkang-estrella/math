# Reproduction

The supplied `pdtar-source.zip` is source-only. It includes the six byte-identical frozen modules, all ten new Lean modules, validation scripts, and a manifest with source and tool fingerprints. It uses the read-only package cache supplied in TASK.txt and Lean 4.34.1; no lake invocation or network access is needed.

The delivered replay is under `replay/extracted`. To continue or confirm its state:

```
python3 -I scripts/replay.py --resume --steps 4
```

To repeat independently, create a fresh directory INSIDE this lane, copy `pdtar-source.zip` and `scripts/replay.py` there preserving the scripts/ path, and run the following commands in that directory:

```
python3 -I scripts/replay.py --init
python3 -I scripts/replay.py --resume --steps 8
```

Repeat the resume command until all 36 steps pass. It performs 16 strict serial compiles, 16 leanchecker checks, one full declaration audit, and three expected-failure negative controls. Never run two replay drivers concurrently. The driver refuses a pre-existing extraction at initialization and verifies source, tool, archive, recorded log and generated-object hashes at each resume step. It rejects path traversal, duplicate paths and compiled objects in the archive.

Lean receives `-j1 -M3500 -DwarningAsError=true -DElab.async=false`. Each heavy child uses the capped runner: CPU affinity at most 2, CPU 120 s, wall 140 s, sampled process RSS at most 6 GiB, virtual address space 16 GiB, no core dump, MALLOC_ARENA_MAX=2, and lane-local TMPDIR, HOME and caches. The higher virtual limit permits the Lean runtime's reservations; the RSS cap remains 6 GiB. Every replay step has a full log and a resource receipt under `replay/extracted/logs`.

The declaration audit visits every declaration belonging to the 16 local modules, including generated/private declarations. It rejects local axioms, unsafe/partial flags, unsafe recursion companions, implemented_by and extern attributes, and transitive axioms outside propext, Classical.choice and Quot.sound. Audit harness code and deliberately failing negative files are not imported by the mathematical modules.

The mathematical status is partial: read SUMMARY.md and the exact Prop definitions in SmallObligations.lean. A clean replay does not discharge those Props or establish acceptance or novelty.
