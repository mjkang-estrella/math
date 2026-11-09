# W006 rational map and batch detector — parent disposition

2026-10-08. Accepted at the corrected scopes below after reading both full
reviews and checking their delivery/source hashes. Verified new end-to-end
factoring complexity improvement: **NONE**. No numerical experiment, shared
solver edit or Lean proof was performed in these two reviews.

## Rational transition: accepted primitive, fixed scalar-capture menu closed

The [rational-map review](W006-rational-review.md) validates the unit-denominator
transition, its O(k*n^2) map work, and the properly stopped root-sign law.
Sampler cost, parameter acquisition, history storage and failures remain extra.
Sign-dependent extraction is applied only after the invariant scalar stopping
event; conditioning on successful extraction does not preserve the old law.

For h=u+iv, its exact coordinate equation is

    v'=v*(4u^2-(a-1)^2)/((a-1)^2+4a*u^2).

Away from a=+/-1,3, four nonscalar preimages of +/-1 exist precisely when
Q_a=(3-a)(a+1) is a nonzero square modulo p; otherwise there are none.
For every prime p=5 mod12, the complete frozen menu {0,1,3,2,5} has no
defined edge from a nonscalar point into the target. Even adaptive schedules
from that menu retain exactly the initial scalar mass 2/(p-1), at every depth.
This rejects its uniform scalar-capture premise, not denominator factoring,
batch collisions, other parameters or the norm-5R packet branch.

The 60-case screen was omitted before implementation/execution because this
symbolic result already decides its stated falsifier. All sixty entries remain
UNKNOWN/UNSTARTED; there are NO transition tables, measured image sizes or
empirical basins to reuse. Older parent notes describing what such tables
could supply are prospective only.

Fresh uniform parameters also have at most 2/p new scalar-hit probability per
nonhit step and at most 2/p local denominator probability. This independently
confirms the core direct-hit conclusion of the parent's later random-parameter
note. It does not establish a bound for biased parameters or collision energy.

The power-image statements for odd and twice-odd exponents are accepted.
The extension for general E needs v2(E)<v2(p-(-1|p)) on each component.
The reviewed prime-power single-check law and finite stopped sampler masses
retain their precise hypotheses. a=3 cannot introduce divisibility by a new
prime in v; increasing valuations on already divisible components is not a
new factor opportunity after the initial gcd check.
Characteristic-zero nonconjugacy of a=2,5 to power/Chebyshev/Lattes maps does
not supply useful finite-field dynamics.

A concrete constructive reopener is to choose parameters with Q_a a rational
square, for example a=(3-t^2)/(1+t^2) with its denominator paid. This guarantees
a nondegenerate first layer outside exceptional primes, not a growing basin or
fast factorer. It matches the earlier Cayley note's one-layer construction.
A second reopener is separately priced collisions, for which the next accepted
detector supplies an explicit consumer.

## Batch collisions: corrected consumption algorithm accepted

The [batch review](W006-batch-review.md) repairs the original first-full-gcd
failure. Work is on the explicit promise N=pq, distinct odd primes.

1. Globally deduplicate the first list of norm-one residues; keep queries.
2. Build the monic product P and evaluate P and P' at all queries.
3. Use P(y) for a query not in the first list; use P'(y) at a shared global
   value. This removes its unique self-match with no coefficient division.
4. A proper norm gcd returns a factor. A full norm gcd admits one bounded
   product-tree descent, omitting the self-leaf by the same derivative rule,
   or one scan of nonself leaves. It must find a proper leaf on this promise.

For distinct-prime N, full norm gcd of a norm-one difference means equality
in the whole quadratic algebra. Thus every remaining nonunit leaf is proper.
This implication fails over prime powers and is not silently generalized.
Global deduplication preserves existence of useful pairs; no iid claim is
made for the deduplicated list itself.

Monic Newton division over (Z/NZ)[i], Kronecker packing and fast integer
multiplication give K*poly(log N+log K) bit work and batch space. No FFT-root
or arbitrary coefficient-inversion oracle is used. Ordinary schoolbook
polynomial timings would not certify that fast envelope.

For independent accepted samples with a product CRT law and sign symmetry,
c_l=sum mu_l(z)^2 lies between 1/m_l and 1/2. The reviewed exact second moment
proves success >=1/11 at K>=c_p^(-1/2); the repaired detector finds the pair.
A computable survival lower bound and an explicit acquisition cap retain
success >=1/22. Early factors are handled by a virtual continued process,
not by incorrectly conditioning the accepted law on absence of early factors.

The paid identity-map control, with an N-only doubling schedule and capped
sampling, has expected sqrt(p)*poly(log N) bit work for distinct odd semiprimes.
This is a known scale and not a new complete all-input factoring theorem.

The relevant normalized comparison uses full accepted-output cost A_eff,k,
identity cost A_eff,0, setup, and c_*=max(c_p,c_q):

    modeled cost ratio = (A_eff,k/A_eff,0)/sqrt(m_p*c_*).

A ratio tending to zero, with all overhead included, is needed for an
asymptotic gain in this model. The shorthand “energy must beat squared cost”
does not omit sampler cost, rejection probabilities or the other component.
It is not a factoring lower bound or a prohibition on other early events.

The parent's square-first decoder remains a separate provisional alternative.
The accepted derivative repair already supplies a complete consumer for this
promise, so no redundant audit or implementation of that alternative is
selected merely to add another report.

## Next computation

Keep this detector as a paid reference. Reopen a map only with an explicit
distribution/cost change addressing the accepted ingress and energy gates.
The parent has independently selected W007's nested split norm circuit,
including an actual eight-root example and a concrete acquisition problem
for the next stage. That branch seeks many directly testable zeros and does
not assume this collision distribution is favorable.

