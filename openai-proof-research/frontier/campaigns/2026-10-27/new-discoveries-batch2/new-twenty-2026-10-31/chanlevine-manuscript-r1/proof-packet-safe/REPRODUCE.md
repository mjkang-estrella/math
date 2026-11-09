# Reproduction

Use the provided Lean 4.34.1 binaries and the read-only package cache at the absolute paths in scripts/build.py. The mathlib revision is d13f23b723b8a846827a245b89c10fc7d3f11612. No network, lake update, git operation, package modification or upstream build is needed.

The delivered source archive contains exactly 75 formal/*.lean files, Python replay scripts, the endpoint source template stored as text, the merge/source manifests and these instructions. No compiled Lean file is shipped. All 74 inherited modules retain their packet bytes; ChanLevineFinal.lean is the only added formal module. Audit/control sources are generated separately in the extraction's tmp directory and do not enter the endpoint's imports.

Run from this lane only:

```bash
python3 -I scripts/replay.py
```

The driver creates a unique, empty replay directory under the lane, safely extracts the archive, verifies all source hashes against merge-manifest.json plus the final module manifest, and invokes the strict serial build and validation. It stores a replay receipt at logs/latest-replay.json. To resume an interrupted extraction without importing any old artifacts:

```bash
python3 -I scripts/validate.py /absolute/path/to/the/existing/replay-directory
```

Build receipts are accepted only when the entire formal source manifest has the same fingerprint. The audit batches select exact environment names through a string hash set, preserving generated names that cannot be parsed as Lean identifiers. Every module is built in dependency order with `lean -j1 -M3500 -DwarningAsError=true` and then checked with `leanchecker`. The replay rebuilds every module, including inherited control and audit modules. Each invocation has a unique retained log.

scripts/cap.py sets CPU affinity to two CPUs, CPU time 120 seconds, sampled aggregate process-group RSS at most 6 GiB, and wall time 140 seconds per child. The build environment sets MALLOC_ARENA_MAX=2 and lane-local TMPDIR and XDG_CACHE_HOME. One expensive process runs at a time. Sampling does not exclude shorter unobserved RSS transients. The small replay coordinator can run longer than one child; the caps apply separately to every expensive Lean/checker process.

The final audit uses capped batches of at most 256 declarations. It starts from every local declaration in the transitive module import closure of ChanLevineFinal. It includes generated/private declarations, reads types and values with allowOpaque := true, and includes constructor edges. Python follows the emitted dependency lists to schedule every reachable declaration, then independently traverses the completed graph from the emitted root set and requires exact equality with the audited set. It rejects unsafe, partial and _unsafe_rec declarations in that closure; local extern/implemented_by entries must also be absent. Upstream executable metadata is inventoried separately, not represented as zero. Only propext, Classical.choice and Quot.sound are allowed as reachable axioms. The scope is the dependency closure of all local declarations, not unrelated declarations from imported tactic/compiler infrastructure.

Three expected-failure controls and two positive controls verify gcd-premise use, positive-level-premise use and the rotor weight convention. Expected-failure logs are retained. They are assembly sensitivity tests, not exhaustive counterexample proofs or a new novelty audit. Root alone adjudicates acceptance.
