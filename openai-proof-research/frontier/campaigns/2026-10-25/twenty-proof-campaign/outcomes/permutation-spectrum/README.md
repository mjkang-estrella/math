# Eigenvalues of permutation-like matrices

Problem: [MathDB362146](https://mathdb.com/p/362146).

Every eigenvalue is zero or a root of unity; zero is an eigenvalue exactly for non-permutation matrices.

The complete formal statement is `PermutationSpectrum.exact_mathdb_conclusion` in `formal/PermutationSpectrum.lean`. The paper is `main.tex`; a release includes `paper.pdf`.

This complete theorem and its source interpretation passed independent review. No worldwide priority claim is made.

From the campaign root, run `python3 verify_outcome.py outcomes/permutation-spectrum`. From a standalone archive, run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. The dependency revisions are recorded in `pins.json`; compiled dependencies are external.

Status: independent review, full Lean compilation and two-page paper QA passed.
