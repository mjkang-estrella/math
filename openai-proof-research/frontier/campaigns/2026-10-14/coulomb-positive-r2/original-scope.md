# Frozen target P: everywhere-positive Coulomb nonattainment

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Third-party reading material remains private and retains its rights.

Status at freeze: UNRESOLVED, not a theorem claim. Campaign remains 4/10.

## Exact target

There exists a real function g in the Schwartz class S(R^3) such that g(x)>0
for EVERY x in R^3 and integral g(x)^2 dx=1, with the following property.
Set rho=g^2 and mu=rho dx. For the fixed three-particle Coulomb cost

 c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1},

where a coincident pair has infinite cost, let

 E(mu)=inf_{pi in Pi(mu,mu,mu)} integral c dpi.

This minimum is finite and attained. For EVERY pair of Borel maps T2,T3
from R^3 to R^3 satisfying (T2)#mu=(T3)#mu=mu,

 integral c(x,T2(x),T3(x)) dmu(x) > E(mu).

The left side may be infinite. The infimum over those Borel pairs equals
E(mu), so a sequence of preserving pairs with finite cost approaches E(mu).
No regularity, cyclicity, derivative or finite-complexity restriction is
placed on the excluded maps. No density with zeros, disconnected support,
only positivity on components, approximate marginal condition, changed cost,
nonidentical marginals, or single exhibited non-Monge optimizer replaces P.

## Dependencies and unpaid operation identified BEFORE sustained proof

Accept openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Family 373,
actual thm:main, prop:certificate, lem:common-ball and lem:splitting give a
smooth density WITH gaps, a five-component calibration, and an exact
pointwise mass-domination obstruction. Its thm:riesz already treats every
d>=2 and s>0 with such gaps; changing the interaction exponent is rejected.

The new operation is to retain an exact obstruction to EVERY deterministic
optimizer after filling ALL gaps and tails. One concrete route must complete
the local calibration globally with enough contact triples to carry an
everywhere-positive smooth square marginal, while retaining a positive-mass
central region whose finite branch images have strictly smaller pullback
marginal density. Neither convolution nor convex mixing supplies that
contact/complementary-slackness assertion. Direct-method existence, equality
of infima, ordinary weak stability, and smooth bump algebra are paid operations.

Primary antecedents inspected before freezing: Colombo--Di Marino (author
version 2013), Thm 1.1 and Remark 1.3; GKR harmonic-cost paper 1805.00417v1,
Thm 1.1 and introduction's shared disconnected-component mechanism; GKR
duality paper 2019, Thms 4.2, 5.2, Lemma 5.3, Prop 5.4. None of these inspected
statements preserves this prescribed local contact locus when the marginal
is perturbed. This bounded screen establishes neither worldwide novelty nor
a contribution-gate verdict.

Historical I217 concerns quantitative BV/fractional complexity on the original
five-component density; it remains separate and uncompleted. This target
imposes no complexity bound and cannot use I217's disconnected-support barrier.
F/G, all campaign vetoes and the parent's corrections remain untouched.

## Freeze rule

P is fixed before the sustained proof attempt. Technical lemmas or a failed
construction do not replace it. Report UNRESOLVED if the global construction
or any other proof of P is unpaid. No Lean/manuscript or acceptance here.
