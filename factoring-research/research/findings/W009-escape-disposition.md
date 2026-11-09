# W009 geometric escape — parent disposition

2026-10-08. E (Opus) terminal result consumed. All 25 delivery hashes verified.
Accept the core identities and exact curve-plus-twist supply law, with the
scope corrections below. No candidate run or improved factoring bound.

The [review](W009-escape-review.md) proves the coalesced-square conjugacy,
2-isogeny x-map, two-fold doubling identity and coefficient rescaling.
It verifies 419 symbolic/fixed-small-field checks; these are correctness
certificates and cannot establish asymptotic performance.

For a carried square P=S^2 and anchor y=a^2, the coalesced update is exactly
the square of S -> S-a^2/S. There is no new factor channel for squarefree N,
since gcd(U^2,N)=gcd(U,N). Generic P with a single coalesced anchor instead
has a different sampler and drift, as the review explains. Its identities
must not be used as the odd sampler's identities.

Accept the odd sampler's exact moment law and first-step count. The Fourier
formula uses a signed quadratic-character term and diagonal subtraction;
the parent's absolute-value upper bound remains valid. Only nontrivial squared
characters need the spectral bound. The equation with output +2a uses
1+-sqrt(2); allowing output -2a adds -1+-sqrt(2). This is a possible local
alignment condition, not an impossibility or a free acquisition rule.

For E:Y^2=X^3+A X^2+B X, the accepted coherent schedule has
P_(2k)=4^k x([2^k]Q). It duplicates W001 dynamics Card 3. The dual step
requires only the sum and product of its two target roots, so no square
root is needed for this schedule. The square-anchor parameterization is
needed only for the proposed alternative kernel selections, not doubling.

For every m>=1, fixed good curve and uniform affine x, accept

    h_m = (|E(F_p)[m]| + |E^d(F_p)[m]| - 2)/(2p).

The curve/twist overlap at rational 2-torsion makes this exact, including
m=1. Kernel size at m=2^k saturates at the 2-primary subgroup; geometric
degree growth is not rational pole growth. Accept the review's odd-stage
coset law as well. The final-denominator formula and per-stage stopped
formula describe different protocols. For denominator-only stopping,
with first-pole stages tau_p,tau_q, success means unequal first-pole times
with at least one within budget. Its fixed-curve probability is

    1 - sum_(j<=D) Delta h_p(j) Delta h_q(j)
      - (1-h_p(D))(1-h_q(D)).

Numerator tests and coefficient gcds are additional channels. The fixed
N=143 certificate is not a work comparison. Fresh CRT inputs are independent
conditional on a fixed curve; adaptively survived histories are not freely
independent.

Supplementary claims require these qualifications:

- The displayed rational order-four point on the explicit target curve
  and its full 2-torsion give divisibility of the group order by eight.
  This is known ECM torsion structure, not a new complexity bound.
- The odd schedule c -> -4c keeps a quadratic twist of Y^2=X^3-X.
  Its unordered curve/twist pair is independent of its nonzero anchor.
  For p=3 mod 4, the review's even-stage pole formula
  (gcd(p+1,2^(k+1))-1)/p must be restricted to k>=1. At k=0 the
  initial identity map has no affine pole, so h_0=0. Use the general
  kernel formula when an endpoint convention is in doubt.
- The general dual cycle has a curve fixed WITHIN its chain. That curve
  and its order can depend on the initially sampled r,s. The review's
  final blanket statement that every such order is sample-independent
  is not accepted.
- Containment in ECM scalar multiplication and saturation of the supplied
  schedules are accepted. An unconditional expected-work claim that ordinary
  ECM dominates every version, or that one schedule is uniformly faster,
  has not been proved with matched sampling, stopping and gcd channels.
- The rational cyclic-isogeny classification was read only in secondary
  Banwait slides. Keep it a literature lead, not an accepted primary-source
  theorem in this project. It is unnecessary for the supplied order-law
  conclusion, and cannot constrain arbitrary N-dependent finite-field maps.

Constructive consequence: the supplied coherent 2-isogeny route preserves
odd order components. It needs a paid change of group/order or a genuinely
different collision mechanism to create new supply. W010 supplies a distinct
cubic acquisition rule; its merits depend on its own weighted law and costs,
not these rejected or saturated rational-fold proposals.
