# Closed integration interfaces

Import `LiteralPureCoefficient` from this lane's `formal/` directory. All of the
following concern the original definitions in byte-identical imported modules.
Actual kernel-checked type and axiom reports are in `formal/Interfaces.lean.log`;
the exhaustive generated/private declaration reports are in
`formal/DegreeAttainmentAudit.lean.log` and `formal/DegreeAttainmentInventory.lean.log`.

`JacobiShifted.ParameterDegree.h_totalDegree (n : ℕ)`:
`(Midpoint.h n).totalDegree ≤ (n+1)/2`.

`JacobiShifted.ParameterDegree.h_bidegree_eq_zero (n i j : ℕ)`:
if `(n+1)/2 < i+j`, then `(Midpoint.h n).coeff (BinaryFiltration.bidegree i j)=0`.
The general-exponent version is `h_coeff_eq_zero`.

`JacobiShifted.ParameterDegree.h_odd_top (r : ℕ) (hr : 1≤r)`:
`homogeneousComponent r (Midpoint.h (2*r-1)) =
 MvPolynomial.C ((-1 : Midpoint.R)^(r-1)*(catalan (r-1) : Midpoint.R))*Midpoint.P^r`.
`h_odd_top_coeff` gives the coefficient equality for every exponent of degree r.

`JacobiShifted.SourceBridge.scale_homogeneousComponent (n : ℕ) (f : Midpoint.Param)`:
`scale (homogeneousComponent n f)=homogeneousComponent n (scale f)`.
`scaledH_coeff_eq_zero` vanishes above the same degree bound after scaling.
`scaledH_odd_top` transports the complete top homogeneous component.

`JacobiShifted.SourceBridge.scaledH_odd_pure_u (r : ℕ) (hr : 1≤r)`:
`(scaledH (2*r-1)).coeff (Finsupp.single 0 r) =
 rationalBase (((-1 : ℚ)^(r-1)*(catalan (r-1) : ℚ))/(2 : ℚ)^r) *
 (MidpointRational.w*t)^r`.
Here `t=w+x` is the existing `SourceBridge.t` and `rationalBase` embeds rational
constants in the quadratic algebra. This is an equality over the rational
algebra, with no integral-divisibility transport through the halves.

`JacobiShifted.SourceBridge.literal_pure_primitive (r : ℕ) (hr : 1≤r)`:
`(L (2*r-1)).im.coeff (Finsupp.single 0 r)=purePrimitive r`.
The derivative, tau-oddness and midpoint value of `purePrimitive` are proved in
`PurePrimitive.lean`. The identity uses the existing literal finite logarithm
and the proved normalized uniqueness theorem.

`JacobiShifted.SourceBridge.sourceKappa_pure_u (r : ℕ) (hr : 1≤r)`:
`(sourceKappa r).coeff (Finsupp.single 0 r) =
 (catalan (r-1) : ℚ)*binomialOddSum (r-1)/(2 : ℚ)^(4*r-2)`.
This is the mandatory literal endpoint. Its only hypothesis is the source
order restriction `1≤r`. There are no sequence, derivative-identification,
primitive-existence, or normalization premises.
