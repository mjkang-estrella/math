# Exact literal endpoint and mapping

```lean
PolynomialConvexity.source_conjecture : PolynomialConvexity.SourceConjecture
```
The byte-identical inherited SourceConjecture unfolds to:
```lean
∀ n L d : ℕ, 2 ≤ n → 2 ≤ L → 2 ≤ d →
  ConvexOn ℝ (simplex n L) (sourcePolynomial n L d)
```
`Edge n L` is every L-subset of Fin n. The finite sum is over every function Fin d → Edge n L, allowing repeated edges. `coefficient` is the product over every inclusive prefix-union reciprocal, and `weight` is the product of the tuple weights. `sourcePolynomial_eq_quotients` identifies this with the source product of quotients. `simplex` is all nonnegative weight functions whose sum equals one. There is no L≤n or degree bound. Fin n merely relabels the source [n]. Empty E, including L>n, is covered by the full theorem (and the inherited direct empty-simplex proof).

Source: arXiv:2009.04510v1 Eq. (2), Section 3 Conjecture 1; published SIAM J. Optim. 31(3), DOI 10.1137/20M1369592, Eq. (1.1), Section 4 Conjecture 1. Both actual primary text bodies and the MathDB r40 literal record were read. The final-union-only p_d is a different polynomial.

`mixed_moment` universally equates the actual concrete integral of every mixed lifetime product with symCoefficient; `moment_identity` gives the actual integral of the dth power as d! times the source polynomial for every signed weight vector. `sourcePolynomial_convex_orthant` divides by positive d!; `source_conjecture` restricts to the literal simplex. No missing analytic statement is an extra hypothesis.
