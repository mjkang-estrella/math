# Proof and dependency map

1. `ParameterDegree.lean`: a coefficient additive map cannot introduce support;
   hence its total degree is at most the original degree. The two-term initial
   polynomial has degree at most one. Strong induction applies the actual
   `Midpoint.h_recurrence`, the product degree inequality, and the elementary
   floor inequality for the two convolution indices. The zero index is handled
   directly. `top_mul` proves coefficientwise that multiplication at the sum of
   two degree bounds sees only the two top homogeneous components.
2. `CatalanTop.lean`: `oddTop k` is explicitly the degree-(k+1) component of
   `Midpoint.h (2*k+1)`. Split the actual convolution into even/even and odd/odd
   indices. The proved bounds kill the derivative and every even/even term.
   `top_mul` identifies each remaining term. Strong induction, the actual
   mathlib `catalan_succ`, and exact sign/power identities solve this convolution.
   Thus `h_odd_top` is a theorem about the constructed integral h, not about an
   assumed sequence of leading terms.
3. `ScaledTop.lean`: the existing substitution maps each parameter to a
   homogeneous linear polynomial over QAlg. Homogeneous evaluation preserves
   degree; monomial/additive induction then proves that scale commutes with
   every homogeneous projection. Apply this to `h_odd_top`. Write the scaled
   potential as u*(w*t)/2 + v*(w*tInv)/2. A finite binomial expansion gives its
   pure-u coefficient, producing the exact factor 2^(-r).
4. `PurePrimitive.lean`: define exactly the finite primitive suggested in the
   assignment. The genuine derivation's power rule and delta(t)=-w*t cancel
   each odd denominator. The finite binomial theorem and 1+t^2=2*w*t give
   delta(p_r)=-Catalan(r-1)*(w*t)^r/2^r. Tau sends t to -t, so p_r is tau-odd.
   The existing midpoint sends t to one, so its value is the literal finite
   binomialOddSum times Catalan(r-1)/2^(2r-1).
5. `LiteralPureCoefficient.lean`: the imported
   `imaginary_logarithmic_derivative_odd_coeff` identifies the derivative of the
   actual finite L coefficient. The product of its two signs is -1. The
   imported `MidpointRational.normalized_unique` now identifies that coefficient
   with p_r. The imported `literal_imaginary_normalization` commutes midpoint
   with the literal sourceLogCoeff. Finally unfold only sourceKappa's existing
   positive-order definition and combine the two factors 2^(-(2r-1)).

Imported mathematical foundations are copied byte-identically from the frozen
root formal directory specified at commit
`8bf3e7569bfd0e9027f6f6ec63b124842ac414bf`. The particular bridges are the already
closed `LogRiccatiIdentification.lean`, `MidpointPrimitive.lean`,
`RiccatiScale.lean`, and their transitive imports. `BinomialOddSum.lean` is
available unchanged; its valuation theorem is not needed to prove the formula.
The actual Catalan module is
`Mathlib.Combinatorics.Enumerative.Catalan.Basic` in the pinned mathlib.

No analytic interchange, infinite summation, changed source definitions, or
integrality assertion after division by two enters the proof.
