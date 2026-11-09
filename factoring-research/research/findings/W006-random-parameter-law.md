# W006 uniform fresh parameters: direct-capture obstruction

2026-10-08. Parent symbolic continuation, PROVISIONAL pending review. No
experiment, new parameter menu, or change to the live fixed-map protocol.

A tempting repair to a fixed map's dead cycles is to draw a fresh uniform
a modulo N at each step. This does give an executable schedule without any
group-order oracle. Its direct fixed-point capture, however, has an explicit
per-step cost barrier.

Fix an odd prime p and h in H_p. If h^4!=1, the map
a -> F_a(h)=h*(h^2+a)/(a*h^2+1)
is a nondegenerate fractional linear function over the quadratic algebra.
Each equation F_a(h)=+1 or -1 has exactly one legal a in F_p:

    a_plus=1+h+h^(-1),     a_minus=1-h-h^(-1).

The traces are scalars in F_p. They are distinct because h+h^(-1)!=0.
The factorizations in the parent note show their denominators are nonzero
in the nonsplit field and units in the split algebra when h^4!=1.
Equivalently, in the split model h=(t,t^-1), excluding h^4=1 excludes
t=+/-1 and t^2=-1. All factors in those denominators are then nonzero.

For h=+/-1, the map stays at that same sign wherever defined. For h=+/-i,
the map is -h wherever defined, so it alternates between these points and
never reaches +/-1; a=1 is the excluded denominator. These are all
fourth roots in H_p: the cyclic group has exactly four because
4 divides p-(-1|p). No larger field-root set has been counted.

Consequently a fresh uniform finite scalar a has direct target probability
exactly 2/p from each generic state, zero from the non-target fourth roots,
and at most 2/p before first arrival from any non-target state. Starting from
uniform H_p, the probability of having reached +/-1 within k steps is at most

    2/(p-(-1|p)) + 2*k/p.

Premature denominator failures or a global stop at another prime can only
reduce this arrival event. Conditioning on surviving them changes the law;
do not divide away that cost and reuse the same bound as a conditional claim.

Likewise Norm(a*h^2+1), as a polynomial in the fresh scalar a, has degree two
and constant term 1. It has at most two roots in F_p, so a local denominator
failure has probability at most 2/p at any step. Across a semiprime pq,
the union bound prices both local denominator and direct-root events by
O((k+1)*(1/p+1/q)). For this direct extraction schedule, obtaining constant
success on balanced factors therefore requires k=Omega(p), as a lower bound
on the total number of uniformly refreshed parameter steps, including restarts
and initial-sample draws. This statement counts uniform sampler early factor
events separately; their exact law must be inserted before a complete bound.

This is not an obstruction to the fixed a=2 or a=5 screen, to biased schedules,
to a batch collision mechanism, or to all rational dynamics. It identifies
which computation must change: fresh uniform parameters do not provide
fast attraction. A proposed adaptive replacement must specify a charged,
sign-invariant bias, rather than assume that shaking loose a cycle increases
useful mass for free. No claim about the batch collision energy is inferred
from this direct-hit union bound.

