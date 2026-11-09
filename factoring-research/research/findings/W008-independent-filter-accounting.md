# W008 — complete restart accounting for independent-label pair filters

2026-10-08. Parent refinement, corrected after independent four-list review.
No experiment or factoring improvement. This is a scoped computation bound
for materializing retained pair lists before their consumer, not a general
factoring lower bound.

Let rho=1/p+1/q-2/(pq). This counts divisibility by exactly one of p,q;
the earlier p-only probability a=(1/p)(1-1/q) was insufficient as an upper
bound for a consumer allowed to return either factor. In the explicit
CRT-label filter of W008, suppose the
two retained pair lists have mean record counts L and R. They are built
from disjoint input lists, so the label selection counts are independent.
All labels are independent of the complete residue data modulo N. The
expected number of useful cross matches is therefore exactly rho*L*R.

By the union/first-moment bound, the trial success probability s is at most
min(1,rho*L*R), regardless of dependencies among matches. The consumer cannot
succeed without a useful retained match. This statement excludes unrelated
early gcd channels; those would need their own separate accounting.

This implementation materializes both lists before searching them. Its
expected record-writing work w is at least L+R. For independent repeated
trials of the same procedure, the renewal identity gives expected work
w/s, even if a trial's cost and success are correlated. Therefore

    expected record work >= (L+R)/min(1,rho*L*R) >= 2/sqrt(rho).

Proof: put t=sqrt(L*R) and use L+R>=2t. If rho*t^2<=1, the quotient is
at least 2/(rho*t)>=2/sqrt(rho). If rho*t^2>=1, it is at least
2t>=2/sqrt(rho). Since rho<=2/p, the bound is still Omega(sqrt(p)).
Zero-sized lists cannot succeed. This covers both rare-success restarts
and constant-success trials; taking smaller retained lists does not evade
the charged work. Input generation, sorting/bucketing, rejected pairs and
the detector only increase this implementation's cost.

For equal original lists and the zero-label filter, L=R=K^2/M, recovering
the threshold in W008. No concentration of retained-list counts is needed
for this expectation argument. An adaptive procedure changing parameters
or detecting a factor before materialization is outside this fixed-trial
claim and needs its actual work/success law; do not generalize the result
to such algorithms without proof.

Constructive interpretation: these labels remove candidates independently
of hidden divisibility. To improve time one needs either a filter with a
proved arithmetic correlation that raises useful matches per retained
record, or a detector that avoids representing both retained lists. The
latter is the scalar-resultant computation selected for W008. The argument
does not show that such a detector is impossible.

## Primary-source scope for the current polynomial computation

The parent subsequently checked Theorem 1(1), Proposition 2's first case,
Corollary 1 and Lemma 4 / section 3.2 of Bostan--Flajolet--Salvy--Schost:
https://cs.uwaterloo.ca/~eschost/publications/BoFlSaSc05.pdf .
They give the composed-sum computation in O(M(d)) field operations when
the characteristic is zero or greater than d, with d the product of input
degrees. For W008 this is d=K^2, so the theorem does not supply a
subquadratic-in-K routine. Composite-ring divisions, resultants and full-gcd
recovery remain the separate assigned audit. No lower bound for a
scalar-only resultant follows from the polynomial output size.
