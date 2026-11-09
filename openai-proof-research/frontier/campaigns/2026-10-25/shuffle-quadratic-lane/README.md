# MathDB369280: the quadratic shelf-shuffle eigenvector

Completed Lean proof for every n>=3 of the exact source eigenpair `Mv=(1/4)v`, with `v != 0` and eigenspace dimension at least one. Main theorem: `ShuffleQuadratic.quadratic_hasEigenvector` in `formal/ShuffleQuadratic.lean`.

The matrix is the bottom-draw single-shelf kernel from Clay, arXiv:2507.10294v1, Theorem 1.1. The vector is exactly Conjecture 1. One-based indexing is explicitly bridged in Lean. The proof establishes the finite quadratic binomial transform by Pascal induction and proves the reflected finite-sum reindexing; it assumes neither moments nor an eigenvector equation.

**Novelty limit:** Tripathi, arXiv:2602.07920v1, Theorem I already implies this assertion. This package supplies a checked elementary proof, not a new-to-literature theorem. Source and mathematical self-reviews are in `notes/`; independent campaign review remains for the parent.

## Rebuild

From this directory:

```sh
python3 verification/verify.py
python3 verification/exact_check.py
python3 verification/mutation_checks.py
```

The verifier accepts `--lean-bin /path/to/lean` and `--packages /path/to/.lake/packages`. Defaults use the supplied Lean 4.34.1 toolchain and pinned campaign mathlib packages. It compiles a byte-identical source copy in `build/`, generates complete declaration/axiom checks, compiles with warnings treated as errors, and records `build/audit.json`. No dependency files are written.

- `formal/ShuffleQuadratic.lean`: complete 16-declaration proof.
- `formal/Checks.lean`: full declaration and axiom checks.
- `formal/pins.json`: compiler, mathlib, and transitive dependency revisions.
- `build/`: fresh compilation, axiom, exact-rational, and mutation evidence.
- `paper/main.tex`: complete mathematical paper source; PDF not built.
- `sources/`: MathDB snapshot and retrieved versioned primary-source HTML.
- `notes/source-review.md`: exact source mapping and duplicate-result assessment.
- `notes/proof-review.md`: implementing agent's review and coverage limits.

No Git state, shared indexes, or neighboring outcomes were modified. All package writes are under this lane. This is one distinct target; the general binomial identity and spectral corollaries are supporting results, not additional campaign outcomes.
