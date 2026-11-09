# W012 — square-coordinate relations from convex support queries

2026-10-08. Parent constructive continuation; PROVISIONAL. No numerical
performance experiment or improved factoring bound. This uses nearby
product data as relations instead of expecting a descent to hit a factor.

## A changed computation, with explicit acquisition

Ordinary nearby products u*v=N+r leave two potentially large unfactored
coordinates. Replace the first coordinate by a known square. For each
integer v in [1,B], define

    t_v=ceil(sqrt(N/v)),       r_v=v*t_v^2-N.

Use exact integer square-root comparisons, not floating-point rounding.
Then

    (v*t_v)^2 = v*r_v (mod N),                            (1)
    0 <= r_v < 2*sqrt(N*v)+v.                             (2)

If v and r_v factor over a prescribed base, this is a standard
square-congruence relation. Every factor of v<=B is in the base of all
primes <=B. A gcd with N is tested before treating a residue as a unit;
zero residual and square/perfect-power cases require their ordinary
handling. Relation dependencies still need their actual signs, exponent
parities, square-root assembly and proper-gcd recovery. Smoothness,
useful dependencies and all restarts are not free.

The region

    t>=1, 1<=v<=B, v*t^2>=N

is convex: it is the epigraph v>=N/t^2 on t>0, intersected with bounds.
Bound t by ceil(sqrt(N)) for a finite query. A positive linear objective
a*t+b*v can therefore be minimized by the same fixed-dimensional
convex-semialgebraic machinery under W012 A's review. For fixed v,
the minimizing t is exactly t_v. The intended saving is to choose useful
multipliers among many v through one paid query, rather than enumerate
all of them. It is NOT an oracle minimizing the residual itself.

A direct residual minimization is not covered by that theorem:
level bands for v*t^2-N are nonconvex. Neither the existence of a small
residual somewhere nor fixed dimension supplies that missing operation.

## Exact small-multiplier geometry

Write h(v)=sqrt(N)*v^(-1/2) and t_v=h(v)+e_v with 0<=e_v<1.
For interior v, the second difference of h satisfies

    w_v^0=h(v-1)-2h(v)+h(v+1)
         >= (3/4)*sqrt(N)/(v+1)^(5/2).

The integral second-difference kernel has total weight one and
h''(x)=(3/4)*sqrt(N)*x^(-5/2). Rounding gives exactly

    w_v=t_(v-1)-2t_v+t_(v+1),       |w_v-w_v^0|<2.         (3)

Consequently all these discrete points are strict lower-hull vertices if

    (3/4)*sqrt(N)/(B+1)^(5/2) > 2.                       (4)

This includes B=N^o(1) for large N. In this regime the convex optimizer
does not skip a sparse subset of unusually good multipliers: every v is
a vertex. It can still select a vertex quickly; that is a different claim
from producing better residuals.

More precisely define g_v=t_(v-1)-t_v. For objective t+lambda*v,
the normal interval for interior v is

    g_(v+1) <= lambda <= g_v,

and its length is exactly w_v>0. With B>=3, draw an integer J uniformly
from g_B,...,g_2-1 and set lambda=J+1/2. Then each interior v=2,...,B-1
is chosen with exact probability

    Pr(v)=w_v/(g_2-g_B).                                 (5)

There are no ties at these half-integer slopes. A binary search in the
strictly decreasing g_v sequence implements this sampler using O(log B)
exact t_v evaluations, plus O(log N) random bits in expectation and their
ordinary rejection-sampling cost. No generic optimizer is needed for
this specified sampler.

Let W0=sum_(v=2)^(B-1) w_v^0 and define the reference law Q(v)=w_v^0/W0.
For epsilon=8*(B+1)^(5/2)/(3*sqrt(N))<1, (3) gives

    (1-epsilon)/(1+epsilon)
      <= Pr(v)/Q(v) <= (1+epsilon)/(1-epsilon).           (6)

The same bounds hold for probabilities of ANY subset of these multipliers,
including a set defined by tiny residual or smoothness. The reference law
depends on the smooth curvature profile; the common sqrt(N) cancels from
its normalized weights. This is an exact comparison, not an assumption
that residual fractional parts are random. Uniform normal-direction
sampling therefore cannot amplify a residual-selected event by an
unbounded factor over this explicit multiplier weighting in regime (4).

This does NOT reject all adaptive direction choices or all support-based
relation generation. Choosing directions using already observed residuals
has a different law and all of its observations must be priced.

## Complete-cost gate and comparison

One accepted row (1) has unknown residual at most the scale sqrt(N*B);
its square-class data are v and r_v. The known-square coordinate removes
one opaque large integer, which is a real simplification from u*v=N+r.
But simply generating these rows has no established asymptotic advantage
over a square sieve. If B=N^o(1), the generic norm envelope remains
N^(1/2+o(1)); the curvature sampler does not prove frequent norms
N^(1/2-delta). No smoothness probability, relation rank or factoring
success bound has been established.

If a revised selector were to produce unusually small B-smooth r_v often,
total cost must include the selector's paid observations, base generation,
sieving/factoring of residuals, enough independent useful rows, linear
algebra, square assembly, proper-factor probability and retries. A useful
primitive can be compared with existing quadratic-sieve multiplier/
polynomial selection only after its primary prior art is checked.
This note makes no novelty claim for the congruence (1) or multiplier
sieving; it records the specific convex-query construction and its
normal-direction selection law.

The next mathematical test is (3)-(6) and the applicability of the
convex query, not a favorable-seed factoring benchmark. A promising
revision would have to exploit a materially different statistic or
shared computation that actually concentrates on useful residuals.
No larger run or new package is selected.
