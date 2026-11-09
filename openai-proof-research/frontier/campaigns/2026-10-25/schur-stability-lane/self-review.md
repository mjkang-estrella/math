# Implementation self-review

Status: complete for the requested s=t=1 counterexample. Independent parent review pending.

## Source match

- Read the actual frozen arXiv v1 HTML, not only the MathDB summary.
- Confirmed Conjecture 1.1's primitive/stochastic, positive-semidefinite, Perron-weighted and row-bound hypotheses.
- Confirmed negative B entries are permitted by the paragraph preceding Conjecture 1.1 and Example 1.2.
- Confirmed the exact order of multiplication in both operator formulas.
- Credited Shivam Patel's posted family and identified this witness as s=1. No novelty claim or verification of the full posted parameter family.

## Mathematical and formal checks

- W: entrywise nonnegative, row sums 1, W^2 strictly positive, full complex spectrum {1,-1/4}, radius 1.
- pi: strictly positive, sums to 1, exact left Perron eigenvector for radius(W).
- B: actual symmetric real matrix, positive-definite quadratic form, standard mathlib PosDef and PosSemidef.
- B spectrum: full complex spectrum {1,1/11}, actual mathlib spectralRadius 1, real conversion 1.
- Source side conditions: Be <= rho(B)e, pi^T Be = 1/55 > 0.
- Step: t=1 lies strictly between 0 and 2/rho(B).
- Actual inverse: both multiplication orders checked; matrix inversion operation identified with the displayed J.
- P and R: source-defined operators, then proved equal to displayed matrices.
- Full spectra: P {1,0}; R {1,1/2}; both exact radii 1.
- Eigenvectors: complex standard HasEigenvector proofs include nonzero witnesses; HasEigenvalue derived.
- Spectral bridge: noninvertibility <-> zero determinant; standard finite-dimensional matrix-spectrum/eigenvalue equivalence; library supremum identity gives radii.
- Main theorem bundles hypotheses and both stability failures; separate universal claims also formally negated in dimension 2.
- Both ENNReal and real spectral-radius failures are established.

## Validation

The campaign verifier passes: 77 declarations, Lean 4.34.1, pinned mathlib and all dependency revisions. Source and check modules compile with warnings treated as errors. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the declaration audit. No proof holes or additional assumptions are used.

The paper builds with Tectonic 0.15.0 without warnings. Four final page images were inspected; formulas, tables and references are legible, with no clipping or overlap.

## Remaining gaps

None in the requested concrete theorem or its spectral interpretation. Parent independent review and any campaign integration/publication remain outside this implementation assignment.
