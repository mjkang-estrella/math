# Lean certificate

`Premagic.lean` proves the complete counterexample and the extensions listed
in `../COVERAGE.md`. `Checks.lean` prints every local definition/theorem type
and its axiom dependencies. The conventional invertible-similarity definition
of diagonalizability is also formally related to the explicit definition.

With existing pinned, compiled dependencies:

```sh
python3 rebuild.py --lean-bin /path/to/lean --mathlib-packages /path/to/.lake/packages
```

`LEAN_BIN` and `MATHLIB_PACKAGES` are equivalent environment variables. The
workspace defaults are conveniences; portable copies should specify paths.
The script creates `build/`, recompiles both source files, checks every pinned
dependency, and rejects warnings, incomplete audits and any axiom beyond
`propext`, `Classical.choice`, and `Quot.sound`.

For a fresh installation, install elan/Lean, use this directory's pinned
`lean-toolchain`, then obtain the dependencies with Lake:

```sh
lake update
lake exe cache get
python3 rebuild.py --lean-bin "$(elan which lean)" --mathlib-packages .lake/packages
```

The Lake download step requires network access and can be large. The final
Python script checks all transitive revisions against `pins.json`; fetching
the wrong revision will fail. Source compilation was actually verified in
the supplied environment with existing cached dependencies; a clean network
bootstrap was not separately exercised.

For detailed proof and build review, see `notes/formal-audit.md`. The local
dependency-cache trust boundary is stated there explicitly.
