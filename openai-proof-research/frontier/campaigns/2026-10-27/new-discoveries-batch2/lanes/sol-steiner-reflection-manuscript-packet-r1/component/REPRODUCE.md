Run from this lane, using the supplied pinned local cache:

```bash
python replay.py steiner-source-component.zip verification-fresh
```

The destination must not exist. The archive has only sources/configuration,
no own oleans or compiled objects. The replay verifies its manifest, exact Lean
binary hash, all nine package revisions (mathlib plus eight transitive pins),
and the recorded reused upstream source/olean hashes. It then builds the six
mathematical modules and the exhaustive origin audit serially, using `-j1
-M2700 -DwarningAsError=true -DautoImplicit=false`. It does not invoke Lake,
fetch dependencies, or edit upstream files.

Each Lean stage has CPU210s/wall230s, a process-group RSS kill threshold
2800MiB sampled at a target45ms interval, and file-output64MiB. Python helpers
have AS512MiB, explicit CPU/file limits, BLAS/OMP/MKL1 in Lean's environment;
replay/package have wall alarms. Sampled monitoring cannot exclude unsampled
transients. A helper keeps an unlimited AS hard ceiling solely to launch Lean
with the separate RSS policy; its own enforced AS soft limit is512MiB.

Read `verification-fresh/replay-receipt.json`, all six empty mathematical logs,
and the exhaustive `logs/OriginAudit.log`. The audit includes private/generated
constants from every own mathematical origin, actual fully elaborated types,
transitive axiom closures and actual unsafe/partial/axiom flags. It crosschecks
`env.constants/getModuleIdxFor?` with every `moduleData.constNames` entry.
Only `propext`, `Classical.choice`, `Quot.sound` are permitted.

The archive is deterministic (sorted paths, fixed ZIP metadata). To regenerate
it from this lane's frozen mathematical sources and pinned cache:

```bash
python package.py
```

The local upstream hashes freeze the reused cache; they do not attest that
cached upstream artifacts were independently rebuilt from the public commits.
No external access is needed or performed by these scripts.
