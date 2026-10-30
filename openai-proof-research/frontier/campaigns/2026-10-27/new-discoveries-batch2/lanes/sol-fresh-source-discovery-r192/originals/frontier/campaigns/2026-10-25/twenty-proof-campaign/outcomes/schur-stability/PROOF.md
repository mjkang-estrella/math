# MathDB 370245: exact counterexample to both Schur stability claims

This is an independent verification and formalization of the **s = 1 specialization of Shivam Patel's posted family**, supplied by the parent. No mathematical novelty or priority is claimed. Target: Banerjee and Chaudhury, arXiv:2509.06715v1, Conjecture 1.1. Independent review accompanies the release after acceptance.

## Source interpretation

The conjecture quantifies over primitive row-stochastic W and positive-semidefinite B, with e the all-ones vector and pi a positive left Perron vector:

- Be <= rho(B)e componentwise;
- pi^T Be > 0;
- 0 < t < 2/rho(B).

It predicts rho(P(t)) < 1 and rho(R(t)) < 1 for P(t) = W(I-tB) and R(t) = I-W+(I+tB)^(-1)(2W-I).

**B need not be entrywise nonnegative.** The actual conjecture imposes positive semidefiniteness, its preceding paragraph explicitly permits dropping nonnegativity, and Example 1.2 has negative off-diagonal entries while expressly satisfying the conjecture. The earlier nonnegative-matrix setting does not override this statement. Relevant HTML anchors are `S1.Thmconjecture1` and `S1.Thmexample2`.

## Exact proof

Take

```
W  = [[0, 1], [1/4, 3/4]]
B  = (1/11) [[9, -4], [-4, 3]]
pi = [1/5, 4/5]^T
t  = 1.
```

1. W is entrywise nonnegative, and every row sums to one. Its square is [[1/4,3/4],[3/16,13/16]], with every entry strictly positive. Thus W is primitive. The identity det(zI-W) = (z-1)(z+1/4), valid for every complex z, gives spectrum {1,-1/4} and rho(W)=1. Also pi>0, pi^T e=1, and pi^T W=pi^T; hence pi is the normalized left Perron vector.

2. B is symmetric. For real x=(x1,x2),

   11 x^T B x = 8(x1-x2/2)^2 + x1^2 + x2^2.

   This is positive for x != 0, so B is positive definite, and therefore positive semidefinite. The identity det(zI-B)=(z-1)(z-1/11) gives spectrum {1,1/11} and rho(B)=1. Nonzero eigenvectors are (2,-1) and (1,2), respectively.

3. Be=(5/11,-1/11)^T <= e = rho(B)e. Also pi^T Be = 1/55 > 0. The step is strictly admissible: 0 < 1 < 2/rho(B)=2.

4. Direct multiplication, using the source's actual definition, gives

   P(1) = [[4/11,8/11],[7/22,7/11]].

   Its characteristic polynomial is z(z-1) and P(1)(8,7)^T=(8,7)^T. Thus its complete complex spectrum is {0,1}, and rho(P(1))=1.

5. Define J=[[7/12,1/6],[1/6,5/6]]. Both J(I+B)=I and (I+B)J=I hold, proving J is the actual inverse (I+B)^(-1). Then

   J(2W-I) = [[-1/2,5/4],[1/4,3/4]],

   R(1) = I-W+J(2W-I) = [[1/2,1/4],[0,1]].

   Its characteristic polynomial is (z-1/2)(z-1) and R(1)(1,2)^T=(1,2)^T. Thus its complete complex spectrum is {1/2,1}, and rho(R(1))=1.

Both strict stability conclusions fail at an interior point of the allowed interval. This refutes each universally quantified claim separately. Equality to one suffices: the conjecture requires strict inequality. No approximate eigenvalues or intermediate-value argument is used.

## Formal semantics and proof coverage

`formal/SchurStability.lean` is the sole proof module. The definitions W, B, pi and t are exactly the displayed data, and P and R are defined by the source operator formulas. In particular R is defined using the actual matrix inverse; `actual_inverse` proves its value, and `R_exact` proves the simplified operator.

`complexify` applies the real-to-complex algebra map entrywise. `rho A` is literally `spectralRadius ℂ (complexify A)`, with the library's extended nonnegative real codomain. `realRho A` is `(rho A).toReal`. In this witness all four radii are proved equal to 1 before conversion. The real radius statements `realRho_B`, `realRho_P`, and `realRho_R` and the real inequality failures are also formal.

`spectrum_iff_det_zero` proves spectrum membership is equivalent to det(zI-A)=0 using mathlib's noninvertibility definition and matrix determinant-unit theorem. The determinant factorizations imply **complete complex spectrum equalities**, not just selected roots. `radius_eq_one` derives exact radius one from the library supremum-over-spectrum identity. Thus the radius is not an ad hoc maximum definition and no missing spectral bridge is assumed.

`eigenvalue_iff_spectrum` proves the standard finite-dimensional equivalence between matrix algebra spectra and `Module.End.HasEigenvalue` after conversion by `Matrix.toLinAlgEquiv'`. `P_complex_eigenvector` and `R_complex_eigenvector` verify eigenvalue-one equations **and nonzero vectors**. `P_hasEigenvalue` and `R_hasEigenvalue` use the library's eigenvalue predicate.

The main certificate `schur_counterexample` bundles all source assumptions, positive definiteness, the strict permitted step, and both failures. `SourceHypotheses`, `ConjectureP`, and `ConjectureR` state the normalized dimension-two versions of the source assertions. `both_conjectures_false` proves their separate negations. Dimension two suffices to refute a conjecture over arbitrary finite dimensions; normalization just fixes the irrelevant positive scaling of pi.

## Attribution and boundaries

The frozen MathDB reply by Shivam Patel, 2026-08-20, has identifier `5a30dc24-61b4-49cc-a6de-ee5f67a71bf3`. Its family uses v=1/(5-s), W_s=[[0,1],[v,1-v]], and the same B. At s=t=1 this is precisely the present example. The reply's additional claims for s<t and arbitrarily small thresholds are not needed and are not asserted to have been formalized here.

This artifact establishes no new-to-literature theorem or priority claim. It does not contradict the paper's separate local or special-case results. It uses no theorem from the pinned OpenAI manuscript repository; the repository provenance rules and immutable revision were read, but no upstream mathematical assumption is needed.

## Reproduction and audit

From an extracted release directory (use `../../verify_outcome.py` in the campaign checkout):

```
python3 verify_outcome.py .
```

The release includes the campaign verifier and pinned dependencies.

The compiler is Lean 4.34.1. `pins.json` records the mathlib and dependency revisions. The verifier creates a byte-identical isolated source copy, treats warnings as errors, checks every declaration, forbids proof holes and non-kernel decision shortcuts, and records all foundational dependencies. `build/audit.json` records PASS, 77 declarations, and only `propext`, `Classical.choice`, and `Quot.sound`. This is a kernel and dependency audit, not an independent mathematical review.

The paper source is `main.tex`; the rendered release version is `paper.pdf`. `metadata.json` records source hashes, exact statement locations, and attribution. `outcome.json` is compatible with the parent campaign verifier.
