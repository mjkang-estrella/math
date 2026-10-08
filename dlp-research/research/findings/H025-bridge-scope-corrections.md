# H025 bridge report: corrected identities and rejected exclusions

2026-10-08. Grok raw report retained. Root identified counterexamples and
assigned a NEW independent native Astra scope audit, now COMPLETED. No new
fast primitive or verified improvement. Do not accept raw blanket exclusions.

## Dyadic abscissa product

2m<q does NOT imply distinct x(jG) for1<=j<=2m: q7,m2 has x(3G)=x(4G).
Distinctness of that entire range requires4m<q. Nevertheless, with P_m(X)
the MULTISET product over1..m, the proposed identity is valid under2m<q:

    P_(2m)(X)=(X−x(mG))*product_(i=1..m) S3(x(iG),x(mG),X)/C_m,
    C_m=−4*y(mG)²*product_(i=1..m−1)(x(iG)−x(mG))² !=0.

Off-diagonal factors contribute m−i,m+i; the diagonal contributes2m and the
extra factor contributes m. Multiplicities survive correctly. Input differences
in C_m are nonzero under2m<q; odd order gives y(mG)!=0. Successive doubling
supplies anchors in O(log T) doublings, correcting the raw unnecessarylog² bound.
Literal dense specialization/interpolation may be quadratic; this does not
exclude all resultant, compressed-product or joint-evaluation schedules.
Efficient membership AND recovery remain missing, not proven impossible.

## Orbit sums: quantifier error and exact counterexample

Distinct poles give degree2k for a sum of translated x-functions as a rational
FUNCTION of a variable P. Equality at the single point P=kG for each different
k does not imply that function identity. The raw exclusion changed quantifiers.

Injectivity on rational points also does not force degree>=q−1. Exact example:
E/F7:y²=x³+x+1 has nonsingular discriminant factor31=3 mod7 and exactly
O,(0,1),(0,6),(2,2),(2,5), hence order q5. Phi=1/(y−3) is regular on all
these points and takes values0,3,5,6,4 respectively. Its degree is3<q−1=4.
Root and Astra checked the finite coordinate/pole argument by hand; no numerical
run was performed. With f(P)=Phi(P)−Phi(P−G), summation telescopes exactly.
This refutes the claimed degree inference, not ECDLP: inversion of the encoded
scalar and an asymptotic advantageous family are not supplied.

## Auxiliary Tate value

For a prime ell!=q, Q=[ell]([ell^-1 modq]Q) belongs to ell E(K).
Its quotient-argument class in a defined Tate pairing is zero, so the pairing
value is trivial on this q-subgroup. Respect argument order and usual field,
torsion and prime-to-characteristic hypotheses. This does not claim triviality
on every point over an arbitrary extension. A small representative of p modq
gives no multiplicative-order bound. The q-level embedding bridge is not solved.

## Disposition

Retain the scoped identities and counterexample. No new test of these three
bridges is admitted without a concrete executable cost advantage. Preserve the
open possibilities instead of inventing broad lower bounds from failed designs.
