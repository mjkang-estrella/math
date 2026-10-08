# H027 polarized quotient: valid kernel, invalid unmarked character

2026-10-08. Initial Opus CardsA/B are retained in H027-algebraic-opus-raw.md.
NEW native Astra geometry/action review completed. Root independently checked
the matrix action and supplied a character-descent counterexample; two subsequent
narrow Astra reviews verified both the example and its size-uniform extension.
These are informal independently checked mathematics, not Lean theorems or runs.

## Valid marked construction

Assume E/Fp has full prime order q>2, q≠p and q∤p−1. Frobenius has distinct
eigenvalues1,p on E[q]; write their geometric eigenlines <G>,<H>, normalized by
e_q(G,H)=zeta. For Q=kG, the subgroup

`K_k=<(G,kG),(-kH,H)>`

has rank2 and is Frobenius-stable. Its generators pair as zeta^(−k)*zeta^k=1,
so it is maximal isotropic for the product polarization. The quotient A_k=E²/K_k
has principal polarization lambda_k with phi_k*lambda_k=q*lambda_product.
The quotient degree is q², distinct from the earlier cyclic degree-q quotient.
Its pairing-defined annihilator can be specified using Q without writing k.
That does not give free kernel representation, enumeration or quotient evaluation.

For gamma=[[a,−b],[b,a]] of norm ell=a²+b² prime to pq,

`gamma*K_k=K_((ak+b)/(a−bk))`.

Interpret a zero denominator projectively. The induced polarized isogeny eta
has degree ell², eta*lambda_k'=ell*lambda_k, and kernel phi_k(ker gamma).
That last subgroup requires a paid quotient map or marking; an unmarked surface
invariant alone does not specify how to compute it. Astra read Robert §§2–3 for
the polarization convention and norm-matrix construction:
https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/articles/polylog_isogenies.pdf

Multiplication by [a+bi] in the quadratic etale algebra over Fq acts on LABELED
parameters. This is a torus torsor on P¹ in the nonsplit case, or on P¹ minus
the two norm-zero parameters in the split case. It is not automatically a
well-defined/free action on unmarked polarized surface isomorphism classes.
Even known identifications k~−k~1/k require compatibility; further identifications
were not classified. Memory-based Steinitz/genus constancy assertions are not
accepted. Exact embedding degree ord_q(p) is retained; no generic size estimate
or extension-degree runtime lower bound is inferred.

From base k=1 the labeled torus element is [(1+ki)/(1+i)]. Its quadratic
character is chi_q((1+k²)/2), not chi_q(1+k²). The missing factor chi_q(2) is
known and repairable. Descent to an unmarked surface is a separate question.

## Exact finite falsifier of character descent

On E/F7:y²=x³+3, x=0 contributes no point; the three cube1 abscissae give RHS4,
and the three cube6 abscissae give RHS2. Hence #E(F7)=13. The trace −5 is prime
to7, so E is ordinary; 13∤6. Take G=(1,2). Hand group arithmetic gives
2G=(6,3) and 3G=(2,2). The rational order-three automorphism alpha(x,y)=(2x,y)
therefore acts by lambda=3 on G and lambda^−1 on the other eigenline.

The polarization-preserving product automorphism diag(alpha,1) sends K_k to
K_(k/lambda), giving polarized A_k isomorphic to A_(k/lambda). Thus A_1 is
polarized-isomorphic to A_9. But modulo13,

`chi(1+1²)=chi(2)=−1`,
`chi(1+9²)=chi(4)=+1`.

Both parameters are away from the split norm-zero values5,8. The relative
character divided by2 also changes. This disproves the proposed universal
unmarked readout, not merely its normalization. No synthetic program or benchmark
was run; this was the candidate-specific cheap algebraic falsifier.

## Uniform conditional extension, not toy extrapolation

Suppose the same rational order-three automorphism exists on the original E,
and its scalar lambda on G has order3 in Fq*. For q>9, a nonexceptional character
disagreement exists by the following separate finite-field argument.

The polynomial F(t)=(1+t²)(1+lambda^−2*t²) is a squarefree quartic, since its
two simple-root sets are disjoint. The smooth projective double cover y²=F(t)
has genus1 and two rational points at infinity (leading coefficientlambda^−2
is a square). Hasse therefore gives

`sum_(t in Fq) chi(F(t)) ≤ 2sqrt(q)−1`.

If chi(1+t²)=chi(1+lambda^−2*t²) at every parameter where both are nonzero,
the sum is q−r with r≤4. Then q−3≤2sqrt(q), impossible for q>9. Disagreement
cannot occur at t=0. Hence some nonexceptional k and k/lambda give isomorphic
polarized surfaces and different character values, uniformly in size under
the stated curve/automorphism hypotheses. This does not assert infinitely many
full-prime-order ordinary j=0 curves or address generic Aut(E)={±1} instances.

## Disposition

Retain the marked quotient and matrix-isogeny identities. Reject the proposed
character as a universal invariant of UNMARKED polarized A_Q. A corrected marked
representation, restricted family or different invariant needs its own paid
extraction/recovery construction and review. No quotient-computation lower bound
or universal inversion lower bound follows. The hypothetical character-oracle
backend is treated separately; its existence is not established here.
Best supported complete work remains square-root; verified improvement NONE.
