# Reproduction

Use Python 3 in isolated mode. The source archive contains only Lean source, scripts, and a manifest; no compiled objects. It uses Lean 4.34.1 and the read-only package cache specified in TASK.txt. No lake build or package modification occurs.

From this lane run:

```
python3 -I scripts/replay.py --init
python3 -I scripts/replay.py --resume --steps 4
```

Initialization requires a fresh `replay/extracted` path and absent replay state. Repeat the second command to advance through 19 serial steps: eight strict compiles in dependency order, eight leanchecker calls, the full declaration audit, and two expected-failure negative controls. At completion it prints REPLAY COMPLETE. The delivered lane already contains a finished replay; to reproduce again, copy just the source zip and driver into a fresh directory inside this lane (or preserve/rename the existing replay directory and state first).

Every resume verifies source hashes, tool binary hashes and a mathlib Basic.lean fingerprint, the zip hash, and all previously recorded build-object hashes. It refuses any unrecorded build object before a step. The manifest records the supplied mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612; no git command is used to query or change it. The shared cache is trusted as supplied, not rebuilt or independently audited.

The driver launches each heavy step through limited.py: affinity at most two CPUs, CPU 120 seconds, wall 140 seconds, sampled process RSS at most 6 GiB, MALLOC_ARENA_MAX=2, lane-local temporary/cache/home paths. Lean receives -j1 -M3500 -DwarningAsError=true and -DElab.async=false. Virtual address space is capped at 16 GiB. The initial optional 8 GiB virtual cap caused thread-allocation aborts despite approximately 3.5 GB RSS; those failed attempts are preserved separately. Raising only the virtual cap resolved this; the requested CPU/RSS/wall caps were retained. Core dumps are disabled in the final driver.

All step logs and resource receipts are in replay/extracted/logs; state records log and object hashes. The audit checks every declaration belonging to the eight certificate modules, including generated/private declarations and generated theorems with upstream-looking names. It checks declaration kinds, safety/partial flags, implementation and extern attributes, unsafe-recursion names and transitive axioms. Audit command code is a validation harness, not part of the mathematical dependency closure.

Negative controls deliberately reject an empty fort and the claim that the empty set power dominates K(2,3). These are syntactically valid, import the completed closure, and fail during proof checking. They do not establish K(2,3) non-uniqueness, which remains part of TwoRemaining. No negative control is included in the mathematical closure.
