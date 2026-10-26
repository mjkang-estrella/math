# A positive counterexample to the premagic diagonalizability conjecture

This package refutes [MathDB problem 336488](https://mathdb.com/p/336488),
Teknomo's Conjecture 7.2. It is new to this project; historical priority is
not established. No result from the stipulated OpenAI corpus is assumed.

The positive integer matrix

```text
M = [4 4 1
     2 2 5
     3 3 3]
```

has every row and column sum equal to 9. It is not diagonalizable over
either the reals or the complex numbers. For `x=(1,0,-1)`, its image is
`Mx=(3,-3,0)`, which is nonzero, but `M²x=0`. A diagonalizable matrix cannot
have this property. The Lean proof establishes that obstruction from the
definition of diagonal similarity, then proves the concrete result.

The paper also explains the positive invertible family `M+tI` (`t>0`),
its doubly stochastic normalization `(M+tI)/(t+9)`, and the extension to
all dimensions at least three. See `COVERAGE.md` for exact formal coverage.

## Files

- `paper/main.tex`: full written proof, attribution and scope.
- `formal/Premagic.lean`: complete formal counterexample and supporting theorems.
- `formal/Checks.lean`: theorem signatures and axiom audit.
- `formal/rebuild.py`: pinned compilation and verification.
- `verification/independent_check.py`: independent exact rational computations.
- `notes/`: independent mathematical, source and formal reviews.
- `sources/source-manifest.json`: source URLs and SHA-256 hashes.
- `COVERAGE.md`: correspondence between paper and formal statements.
- `PROVENANCE.md`: sources, authorship, review and priority limits.

The release archive includes the PDF and verification receipts. Large local
caches, compiled dependencies and third-party source bodies are excluded.
Before rebuilding an extracted release, its complete original inventory can
be checked with `python3 verification/verify_release.py`. Rebuild commands
create additional files, so run the inventory check first.

## Reproduce

Use Lean 4.34.1 and the pinned mathlib/dependency revisions supplied in the
formal directory. The formal README and `python formal/rebuild.py --help`
give the toolchain and package-directory options. A normal Lake installation
of those pinned dependencies can supply the compiled package directory.

```sh
python3 formal/rebuild.py --lean-bin /path/to/lean --mathlib-packages /path/to/.lake/packages
python3 verification/independent_check.py
```

To rebuild the PDF, install Tectonic 0.17.0 and run from the package root:

```sh
python3 verification/build_paper.py --tectonic /path/to/tectonic
```

The first TeX build may need network access for standard TeX files. An
already-populated cache can be selected with `--cache-dir` and used offline
with `--only-cached`. PDF byte identity is not promised across engines or
different timestamps; formal theorem checking and the source hashes are
the reproducibility targets.

Original prose: CC BY 4.0. Original code and Lean: MIT. Third-party sources
retain their own rights. This is an internally reviewed AI-assisted note,
not externally peer-reviewed research. Preparation does not publish the
result to MathDB, Zenodo, or any other service.
