# H013 hybrid review: anchor obstruction and missing noisy recovery

2026-10-08. Grok4.7 independent proposer, native Astra adversarial anchor/HNP
review, root derivation/check. Raw proposal retained. No experiments or new Lean
claims. Verified improvement NONE. The ordinary square-root baseline remains;
its random-walk constants are models, not universal measured guarantees.

## Anchor residual: exact obstruction to its rational branch

Over characteristic p>3 let E:y^2=x^3+a*x+b be nonsingular and let the anchor
A=(x0,y0) be a nonzero odd-prime-order point. Define

    s_A(R)=(y(R)-y0)/(x(R)-x0),  mu(P)=(3*x(P)^2+a)/(2*y(P)).

The proposed residual roots from the line through A with slope mu have
sigma=mu^2-x0, pi=x0^2+a+mu^2*x0-2*mu*y0 and discriminant sigma^2-4*pi.
Root checked the factorization. The chord sum relation alone supplies two
unknown logarithms, not individually usable affine labels.

The discriminant is NOT a square even over the algebraic-closure function field
for this anchor. Here is the native reviewer argument, independently checked:

1. s_A has simple poles exactly O and -A, so degree2. At A the numerator and
   denominator cancel; y0!=0 is essential.
2. mu has four simple poles, precisely E[2]: O and the three nonzero geometric
   two-torsion points. Nonsingularity makes3*x^2+a nonzero at each finite pole;
   p>3 gives the simple pole at O.
3. A rational discriminant root would define a nonconstant rational F:E->E with
   s_A o F=mu. It extends to a morphism of degree2. Translation by -F(O) gives
   an endomorphism phi, so F=phi+T.
4. Pulling back the pole divisor forces points P,P' in E[2] mapping respectively
   to O and -A. Therefore A=F(P)-F(P')=phi(P-P') belongs to E[2], contradiction.

Underlying extension/isogeny facts are stated in Sutherland's
[elliptic curve morphism notes](https://math.mit.edu/classes/18.783/2023/LectureNotes4.pdf).
This is a scoped paper obstruction, not a novel general lower bound. It rejects
the claimed globally rational square-root-free branch. It does NOT exclude
pointwise splitting or an independently supplied cheap labelled rule on a finite
subset. Neither is supplied. No symbolic square-test engine is necessary.

Correct related overclaims: ordinary End(E) need not be Z. Rational self-maps
are endomorphism plus translation, not automatically multiplication[n] as maps.
Three rational samples cannot identify such a map: Frobenius and identity agree
on every rational point but differ as morphisms. Even an endomorphism's usable
scalar eigenvalue must be computable. A guessed generic square-root cost is not
a universal lower bound; none is needed for the obstruction above.

## Coordinate-HNP: exact premise false, biased variant unspecified

x(nG)=x((q-n)G) while scalar top-bit labels differ on many such pairs (already
n1 and n=q-1 in the proposed regime). Thus a universally exact x-to-scalar-top-
bits bridge is false. For normalized2^mu equal bins floor(2^mu*n/q), opposite
labels are complements, so x-only prediction agrees on at most half the nonzero
scalars. Literal fixed-width bit truncation has central-bin exceptions and needs
its own counts; do not silently replace it by normalized bins.

The proposed biased variant is still missing a noise model and recovery
algorithm. Agreement equal to2^-mu does not prove independence; unequal bins
may not even have that chance baseline. A probability excess does not supply
bounded numerical errors for an HNP lattice, and no delta^-2*log(q) conversion
was justified. A finite median or noisy estimate cannot refute a uniform
expected/asymptotic claim without its probability/parameter scope. No 2000-
sample/lattice run authorized. A specified useful leakage and noisy decoder
could reopen a different test, without treating generic bounds as prohibitions.

## Running-sum shepherd: paid operation, no favorable evidence

The proposed pair state(P,Sigma) takes four group additions: one jump candidate,
two for2*Sigma-P, one accumulator update, choosing the smaller canonical candidate.
Labels can be updated exactly and cross-collisions verified. But a hash/partition,
cycle detection/storage and complete restart law must be frozen before execution.
Its four-addition cost requires a substantial useful-collision acceleration
against competent negation-rho, with all failed/restarted paths and memory paid.
No evidence or argument for that acceleration was given. The proposed one-curve,
30-target median versus a heuristic mean is not a decisive falsifier of the raw
uniform expected-work assertion, and group-call-only counting omits the requested
complete work. No run or result is claimed.

The introductory image bound only applies to a selector among specified fixed
bijective branches; image cardinality alone does not establish collision time.
History-dependent pair states are outside that argument. The card is parked for
lack of a supported concentration mechanism, not declared impossible. No inferred
constant hardware ratio, free distinguished-point stopping, or hidden phase rank.
