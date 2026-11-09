# W006 nonmonomial norm-one map: an actual alternative to exponent selection

2026-10-08. Parent construction; NOT independently accepted. No experiment has
run under this note. No new complete factoring bound is claimed.

## Computation

Let N be odd and H={h in (Z/NZ)[i]: h*bar(h)=1}, i^2=-1.
The accepted W005 sampler gives uniform h, or an early proper factor, with paid
caps. For a public scalar a define, when its denominator is invertible,

    F_a(h) = h*(h^2+a)/(a*h^2+1).

Compute z=h^2, A=z+a, D=a*z+1, d=D*bar(D), g=gcd(d,N).
If 1<g<N return that verified factor. If g=N, declare this attempt exhausted.
Otherwise use D^(-1)=bar(D)/d and perform the displayed map.
Each iteration uses O(1) ring operations, one gcd/inverse and O(log N) space;
with classical arithmetic a conservative O((log N)^2) bit cost per step.
Do not expand the degree-3^k rational function: k iterations cost O(k)
ring operations. Generating h and all caps are also charged.

Since Norm(z)=1,

    Norm(z+a) = 1+a*(z+bar(z))+a^2 = Norm(a*z+1).

Thus F_a has norm one on its defined domain. For every scalar r^2=1,
z(rh)=z(h) and F_a(rh)=r F_a(h). The denominator test and its outcomes are
invariant under these signs. A fixed parameter schedule, or a schedule depending
only on sign-invariant history, preserves this property through stopping.
This is a proposal for a proof, including exhaustion, not permission to leak
the accepted h tape to a blinded-root inner solver.

The direct extraction control inspects v in h=u+iv, initially and after each
step. A proper gcd(v,N) splits N. If v=0 mod N, h^2=1, so gcd(u-1,N) may split
N. The full scalar event has mixed signs with probability 1-2^(1-omega(N))
under a root-sign-invariant output law, conditional on that event. Repeated
powers require the precise local ring law and perfect-power handling.
The x*(1+2i)*F(h) norm-5R certificate variant preserves outer-root independence;
its useful field-packet probability remains a separate unpaid question.

## Work this could replace and decisive unknown

Fixed odd powers compress H only through divisors of p-(-1|p), and exponent
acquisition is the known p-1/p+1 bottleneck. This rational map is not assumed
to be a group homomorphism. Repeated unequal fibers could instead concentrate
mass at the two fixed points +/-1. If an explicitly paid poly(log N) schedule
captured inverse-polynomial mass for every prime component, the cost picture
would change. Such a capture theorem is completely unproved.

For a fixed a, the local basin of +/-1, NOT the total image size, determines
this direct mechanism. Cycles disjoint from these points can defeat arbitrary
iteration depth. Degree 3^k is an upper bound on the number of algebraic
preimages, never a lower bound on rational preimages or captured probability.
Bad denominators, repeated roots, parameter exceptional primes, unequal local
basins, per-step work and correlation across restarts must all be paid.

## Explicit structural controls and shortcut failure

For formal h, after cross multiplication,

    F_a(h)-1 = (h-1)*(h^2+(1-a)*h+1)/(a*h^2+1),
    F_a(h)+1 = (h+1)*(h^2+(a-1)*h+1)/(a*h^2+1).

a=0 gives h^3, a=1 gives h wherever the uncancelled implementation is defined,
a=-1 gives -h there. For a=3,

    (F_3(h)-1)/(F_3(h)+1) = ((h-1)/(h+1))^3,

so this apparent concentration map is conjugate to cubing, with chart
exceptions requiring explicit accounting. Do not count it as a new mechanism.

Trying to choose a from z=h^2 to force a scalar output exposes the core gate:

    z*(z+a)^2-(a*z+1)^2
      = (z-1)*(z^2+(1+2*a-a^2)*z+1).

Away from z=1, this formally requires
    (a-1)^2 = z+2+z^(-1) = (h+h^(-1))^2.
The known choices a=1+(h+h^(-1)) and a=1-(h+h^(-1)) force respectively
F=+1 and F=-1 wherever defined. But they use sign-dependent h, not only z,
and encode the answer. Choosing a root independently from z asks for exactly
a modular square-root operation; no cheap selector is provided.
Over a composite, one cannot cancel z-1 unless it is a unit; its nonunit
branches can already supply factors. The reviewer must retain that condition.

## Frozen first falsifier

See W006-rational-map-prereg.md. Exhaust the small prime norm groups and measure
the whole functional graph and cumulative fixed-point basins for a short fixed
parameter menu. This is a primitive screen, not an N-only factoring benchmark.
It can expose dead cycles or cubing conjugacies and distinguish basin growth
from mere image shrinkage. No finite pass establishes a general capture bound.

The parent keeps coefficient-preserving and quaternion-generation work separate;
a failed rational-map basin does not close either route. Primary prior art and
the independence/cost argument are delegated before promoting this construction.

