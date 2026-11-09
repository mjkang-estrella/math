# Complete proof map

## Upper bound on every literal coefficient

1. `HalfSubstitution.substitutionNumerator e` is the integer polynomial
   `(u+v)^(e 0)*(u-v)^(e 1)`. `scale_monomial` proves that root's **actual**
   substitution sends an integral coefficient times the parameter monomial e
   to its lift times this integer polynomial, divided by `2^e.degree`.
   `scale_coeff_expansion` follows by the finite support expansion of the
   original polynomial. No assertion that the half substitution preserves
   integrality is used.
2. `coefficientPrimitive n hn e` chooses a witness from root's already proved
   `h_odd_primitive_existsUnique`. Its derivative and tau-odd normalization
   are proved in `coefficientPrimitive_spec`. The existing closed midpoint
   theorem proves that its midpoint divided by `2^sigma(e.degree-1)` is
   TwoLocal. Choice introduces no existence premise; the existence is proved.
3. `transportedPrimitive` is the finite sum of these witnesses, each multiplied
   by `rationalBase ((-1)^r * substitutionWeight e m)`. The true derivation and
   involution rules prove its derivative is the m-coefficient of
   `(-1)^r*scaledH(2r-1)`, and its tau image is its negative.
4. The actual finite logarithm has that same derivative and tau normalization
   by `imaginary_logarithmic_derivative_odd_coeff` and
   `literal_imaginary_normalization`. `normalized_unique` therefore proves
   `literal_transportedPrimitive`. Taking the actual midpoint and then the
   literal source factor `2^(-(2r-1))` gives `sourceKappa_coeff_expansion`.
5. For every support exponent e of h_(2r-1), the proved zero parameter
   coefficient excludes degree zero. The actual `h_totalDegree` bound gives
   `1 ≤ d=e.degree ≤ r`. No special primitive needs to be postulated off support;
   all sums range over the original finite support.
6. `factorial_valuation` proves `v2((d-1)!)+sigma(d-1)=d-1` from mathlib's
   Legendre theorem with the subtraction bound. Divisibility of factorials
   proves `v2((d-1)!) ≤ v2((r-1)!)`. With E=`dyadicExponent r`, n=`2r-1`,
   s=`sigma(d-1)`, and k=`v2((r-1)!)-v2((d-1)!)`, `exponent_balance` gives
   `E+s=n+d+k`. Every exponent is a natural number with its required bounds.
7. `power_balance` rewrites each scaled summand exactly as
   `((-1)^r * integerCoefficient * 2^k) * (midpoint primitive / 2^s)`.
   The first factor is an integer; the second is TwoLocal by Step 2.
   Closure under products and finite sums proves `sourceKappa_twoLocal` for
   **every** target exponent m, including those outside the resulting support.

## Sharpness at the literal pure-u coefficient

1. The unchanged `sourceKappa_pure_u` identifies the coefficient as
   `Catalan(m)*binomialOddSum(m)/2^(4r-2)`, m=`r-1`.
2. `centralBinom_valuation` uses the actual Kummer digit-sum theorem at (m,m)
   and `sigma_double` to prove valuation `sigma(m)`.
3. `catalan_ne_zero` follows from the positive central binomial coefficient and
   `(m+1)*Catalan(m)=centralBinom(m)`. Applying valuation to that equality proves
   `catalan_valuation = sigma(m)-v2(m+1)` as an integer equality.
4. The existing closed binomial-sum component supplies its nonzero value and
   valuation `m+v2(m+1)`. The actual coefficient is nonzero by multiplication
   and division of nonzero rationals. Valuation product and quotient rules
   now apply with their nonzero hypotheses discharged.
5. Adding the valuations and applying Legendre gives exactly
   `padicValRat 2 coefficient = -dyadicExponent r`.
6. `twoLocal_iff_valuation_nonneg` follows directly from the odd denominator
   predicate, valuation of a denominator, and rational reducedness
   (`Rat.num_or_den_zero_padicVal`). It includes q=0; zero is not discarded.
7. Since E≥2 for r≥1, multiplying the nonzero coefficient by `2^(E-1)` has
   valuation -1. The equivalence in Step 6 proves its denominator is not odd.

`JacobiShifted.source_claim` in `SourceClaim.lean` combines these two closed results using exactly
root's unchanged `SourceClaim` definition. No mathematical gap remains in the
assigned endpoint. Manuscript, independent final review, current novelty
investigation, integration, acceptance, and accounting remain root's tasks.

## Ordinary-proof provenance and limits

The upper-bound reasoning follows the integral midpoint filtration and
normalized primitive construction in `sol-jacobi-riccati-valuation-r4/PROOF.md`.
Its older Laurent/scaling presentation is translated into the already frozen
Lean convention by paying the actual `2^-d` substitution factor explicitly.
The top/source reasoning is already formalized in the frozen degree component,
whose ordinary precursor is `sol-jacobi-shifted-denominator-r3/discovery.md`.
`sol-jacobi-full-preliminary-review-r1/review.md` records the ordinary independent
review and historical objections. Their source paths and hashes are in
`provenance.json`. Historical claims that a formal bridge remained absent are
not reused as current status; the current frozen Lean interfaces are authoritative.
No old GLM antisymmetry, false exact-coefficient statement, finite test, external
valuation oracle, changed literal definition, or analytic identification enters
this component. This lane makes no novelty or acceptance decision.
