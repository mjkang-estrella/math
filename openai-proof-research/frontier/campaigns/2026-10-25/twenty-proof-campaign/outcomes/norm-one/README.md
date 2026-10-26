# The unnormalized eigenvector norm conjecture

MathDB [336487](https://mathdb.com/p/336487), Teknomo Conjecture 7.1, claims
unit Euclidean and Frobenius norms for a dominant eigenvector of a nonnegative
premagic matrix. As written it imposes no normalization.

The positive matrix `[[1,1],[1,1]]` has eigenvector `(2,2)` with eigenvalue 2.
Every complex eigenvalue is 0 or 2, so the exhibited eigenpair is dominant.
Both squared norms of `(2,2)` are 8. This completely refutes the literal
unnormalized statement. A claim specifically about a unit-normalized
eigenvector would instead be tautological and is not refuted here.

This is an elementary normalization correction, not a claim of a novel
spectral technique or a major research advance. It is a distinct MathDB
question from diagonalizability (336488): the matrix here is diagonalizable.

Files:

- `formal/NormOne.lean`: complete counterexample, including complex dominance.
- `main.tex`: written proof and normalization discussion.
- `source.json`: observed MathDB statement and status.
- `COVERAGE.md`: exact formal scope.

From the campaign root, run:

```sh
python3 verify_outcome.py outcomes/norm-one
```

Use `--lean-bin` and `--packages` to override the local workspace defaults.
The proof uses Lean 4.34.1 and the revisions in the campaign `pins.json`.
The verifier builds an isolated copy and records all declaration types and
axioms in the outcome's `build/` directory.

In a standalone release archive, the verifier and pins are at the package
root. Run `python3 verify_outcome.py . --lean-bin /path/to/lean
--packages /path/to/.lake/packages` there. The `primary-reference.json`
records pinned arXiv source URLs and hashes, drawn from the separately
retained source audit; third-party full papers are not redistributed.

Status: independent review, full Lean compilation, and two-page paper QA passed. Original prose CC BY 4.0; original code MIT,
under the same author and terms as the sibling premagic package.
