# Lean certificate

`Matkowski.lean` contains the full result. `Checks.lean` prints every local definition/theorem and all axiom dependencies. `rebuild.py` recompiles sources with warnings treated as errors, checks Lean and all dependency revisions, rejects incomplete declaration audits, and allows only `propext`, `Classical.choice`, and `Quot.sound`.

```sh
python rebuild.py --lean-bin /path/to/lean --mathlib-packages /path/to/.lake/packages
```

The workspace defaults locate the supplied Lean 4.34.1 and cached pinned packages. Fresh network setup is available via the pinned `lean-toolchain` and `lakefile.toml`, but was not separately exercised. The local dependency cache is trusted to contain the compiled versions of the checked clean source revisions.
