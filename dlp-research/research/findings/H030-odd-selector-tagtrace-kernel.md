# H030 C1: odd-selector tag tracing, valid narrow kernel / unverified solver

2026-10-08. Native Sol proposes; native Astra independently checks state algebra
and table size; root checks identity, regular-operation accounting and primary
Bos discussion. Factory Opus primary-art/full-cost review RUNNING, handle in
H030-independent-candidates.md. No implementation, numerical run or Lean claim.
Verified complete-work improvement NONE. H028 execution remains parked.

## Mechanism and exact invariant

Use the accepted H028 normalized q-Miller coefficient h=a/q on the ordinary
prime-order group, with p>3 and q!=p. Its relevant properties are

    h(-P)=-h(P),  h(P+K)=h(P)+h(K)-lambda(P,K),

with explicit identity/tangent/vertical dispatch. Here h is an ODD SIGN SELECTOR,
not a collision key. Ordinary x identifies negation classes. For h!=0 choose
the representative whose canonical integer h lies below p/2. For h=0 choose
by y instead, computing y and paying for it; O gets explicit dispatch.
This defines can_h(P)=can_h(-P), but does not prove any useful-collision law.

Maintain a full origin P0, h(P0), a signed jump vector representing K, and
epsilon in{+1,-1}, with logical state S=epsilon*(P0+K)=can_h(S).
For J=J_(selector(x(S))) set K'=K+epsilon*J. A stored full point K' and its h
allow computation of the ordinary slope lambda(P0,K'), X=x(P0+K'), and
H=h(P0)+h(K')-lambda. Choose delta canonically from H (paid y tie-break at0).
Then

    S'=delta*(P0+K')=can_h(S+J).

Reason: S+J=epsilon*(P0+K'), and canonicalization is negation-invariant.
For labels P0=a0G+b0Q, K'=aKG+bKQ, new labels are
delta*(a0+aK,b0+bK). A full refresh sets P0=S', h(P0)=delta*H, K=O, epsilon=1.
This implements a fixed logical negation-quotient transition independent of
refresh phase, PROVIDED exceptions and cycle escapes preserve that transition.
It avoids H029's cross-phase logical-walk error; it does not inherit rho's law.

Bootstrap h(G),h(Q) via the paid accepted Miller procedure. Propagate h through
all paid jump/table construction, including tangent/vertical/identity cases.
K'=O can reuse the full origin. Precomputation coincidences are neither free
compression nor permission to hide useful recovery/setup work.

## Primary distinction and table gate

[Bos thesis §4.6, pp51–52](https://www.joppebos.com/files/EPFL_TH5291.pdf)
describes x-only tag tracing over cumulative jump sums and identifies y-based
sign selection as its negation incompatibility. Root also read §3.4 of the
112-bit paper from the downloaded primary. C1 addresses that specific premise
using an alternate odd selector. This is not a novelty claim; prior-art review
must include later work and other selectors. Known tag tracing is the baseline.

The full signed cumulative-vector ball of radius tau in r coordinates contains

    N(r,tau)=sum_(j=0)^min(r,tau) 2^j * binom(r,j) * binom(tau,j).

Choose j nonzero coordinates, their signs and positive magnitudes totaling at
most tau; the last count is binom(tau,j). This is a formal-vector count, not
necessarily distinct points. For tau=2, N=2r²+2r+1. A pointer implementation
can need up to2r*N(r,tau-1) transitions; otherwise vector indexing/ranking is
paid. Storing point x,y,h, metadata and optional labels substantially exceeds
the ordinary r-jump table. No table capacity/cache estimate is measured yet.

## Regular arithmetic ceiling and remaining whole-cost gate

An unrefreshed ordinary case omits output y's one multiplication, replacing its
two additions with the h cocycle's two additions. A refresh computes BOTH h
and y. With standard I+2M+S+6A affine formulas before batching, the ideal average
credit over a tau-step block is

    (1-1/tau)*M - (2/tau)*A,

before canonical-sign, indexing, lookup, table construction, cycle/exception,
reporting and verification differences. Finite inversion batches still count.
At tau=2 the arithmetic M credit alone is below10% of5M+S for .8<=S/M<=1.
Larger tau grows the table quickly. A literal extra h fieldword read can consume
the entire sub-one-M credit under equal-unit memory/M pricing; this is a layout
and cost-model screen, not a universal implementation lower bound.

Changing the representative changes the r-adding map. Equivalence to a full-y
implementation of the SAME h-canonical map tests arithmetic correctness only.
Complete-work evidence additionally requires comparison to competent ordinary
negation rho with its own setup/cycle policy. Global h-fibre bounds do not give
visited zero-h frequency; charge actual fallback behavior. No imported random-map
constant, novel exponent, or physical/GPU rate is asserted.

Next gate: one fixed r,tau/layout/exception/cycle contract with positive COMPLETE
cost headroom in an explicit regime, independently reviewed before any bounded
synthetic experiment. Do not build a solver merely because this kernel is valid.

## Completed proposer ledger and other arithmetic attempts

Sol's completed initial report agrees with the algebra and finite-batch average
(4+1/tau)M+S+(I-3M)/n+(6+2/tau)A in the regular block, before extra control.
For a literal sign implementation testing H=0 then H>(p-1)/2, retain raw H and
orientation during a block; negate both y and origin h only on a negative refresh.
Writing E in{0,1} for that refresh sign and Nminus for the comparator's number
of ordinate negations, its specified regular-block difference is

    -(tau-1)M + (2+2E-Nminus)A + tau*C + DeltaL.

C counts the additional zero test; DeltaL includes the explicit extra retrieval,
descriptor and control costs. Different sign/caching implementations need new
ledgers. A cached previous slope permits paid current-y reconstruction when an
exception requires it. No visited zero-h rate or sign-frequency law is assumed.

Other initial mechanisms: persistent denominator powers reduce to known XYZZ
mixed addition (8M+2S), plus invariant key/partition costs; no new full-work gain.
Sol actually read [EFD madd-2008-s](https://www.hyperelliptic.org/EFD/g1p/auto-shortw-xyzz.html)
and [Goundar et al. §2.2/Algorithm1](https://marcjoye.github.io/papers/GJMRV11regpm.pdf).
Plain ordinate-skipping without the alternate selector is known tag tracing,
already accounted for by Bos; it is not a second surviving mechanism.
