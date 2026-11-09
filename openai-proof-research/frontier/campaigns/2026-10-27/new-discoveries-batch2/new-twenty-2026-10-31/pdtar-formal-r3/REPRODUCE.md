# Reproduction

This is a partial certificate, not a completed MathDB endpoint or an acceptance request. `PDTAR.Final` declares `mathdb_353203_conditional` with exactly two explicit rigidity hypotheses; it does not declare the unconditional `mathdb_353203`.

The source-only `pdtar-source.zip` contains 27 modules, the compiler and checker wrappers, bounded runner, resumable replay driver, module order, declaration audit, five negative controls, and a hash manifest. All imports outside PDTAR use the pinned read-only package cache named in TASK.txt. No network or lake command is needed.

To check the supplied replay's state and advance by one bounded subprocess, from this lane run:

```sh
python3 -I scripts/replay.py --resume --steps 1
```

Repeat until it reports `REPLAY COMPLETE`. The provided replay is already complete when handed back. Each invocation verifies source hashes, tool pins, previous log hashes and all current build-object hashes. It compiles in dependency order with Lean 4.34.1, `-j1 -M3500 -DwarningAsError=true -DElab.async=false`, runs leanchecker on each module, audits every local declaration including generated declarations, checks that the audited module set equals the local import closure of Final, and runs five fixtures that must fail with substantive Lean errors. No comparison graph enumeration is used.

For a new replay, copy the source zip and `scripts/replay.py` into a NEW empty directory inside this lane, preserving the script's relative path. Run `python3 -I scripts/replay.py --init`, then the command above with a bounded step count. Do not modify or remove the supplied completed replay or reuse its logs. The init refuses an existing replay directory/state. ZIP member names are checked for duplicates, absolute paths, parent traversal and compiled artifacts before extraction.

The bounded runner sets affinity to at most two available CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB and virtual memory 16 GiB. MALLOC_ARENA_MAX=2, Lean thread count 1, and temporary/cache directories are lane-local. RSS is sampled every 50 ms; transient peaks between samples are not excluded. Only one heavy subprocess is run at a time. Unique nanosecond identifiers name logs, and the runner refuses to overwrite a log. Each receipt records elapsed time, sampled peak RSS, return code and termination reason. Scripts do not change HOME.

`python3 -I scripts/verify_inputs.py` independently rechecks all three archive hashes, all sibling original Lean sources against their verified packets, and every one of the 23 inherited merged source files. This provenance script is supplied separately beside the archive; it needs the three sibling lanes and `frozen-before.json`. Replay itself does not need them.

The inherited modules are byte-identical. Only the six requested base modules are selected from r1; its optional Endpoint and Fidelity modules are excluded. The r2b Reduction modules and ten r2a modules are all included. SmallStatement re-proves the three literal-definition checks from the optional r1 Fidelity module under a new module name and adds the empty-comparison exclusion. No inherited file is patched.

The audit rejects unsafe/partial declarations, `_unsafe_rec` companions, `implemented_by`, `extern`, local axiom declarations, and transitive axioms outside propext, Classical.choice and Quot.sound. The five negative controls are false K(2,3) uniqueness, false K(3,4) non-uniqueness, false uniqueness of the conditional endpoint at s=2, an empty fort, and a corrupted added-edge family that incorrectly accepts a right singleton at t=3. The controls are proof failures, not exhaustive counterexample searches.
