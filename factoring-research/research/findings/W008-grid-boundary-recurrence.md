# W008 — a boundary test for low-order grid recurrences

2026-10-08. Parent derivation AFTER the affine-grid task B was delegated.
PROVISIONAL; not yet independently audited and not part of that task's
frozen original brief. No experiment, solver/Lean change or factoring bound.

## Characteristic-zero polynomial identity

Let
G(X)=product_(u in [0,K)^4)(X+a_1*u_1+...+a_4*u_4)
over Q(a_1,...,a_4), with independent symbolic slopes. Suppose

    sum_(j=0)^r A_j(X) G(X+j*a_1)=0,

where 1<=r<=K, A_r is nonzero, and all A_j are polynomials in X over
this coefficient field. At the K^3 boundary points indexed by
v=(v_2,v_3,v_4) in [0,K)^3,

    x_v=-(r-1)*a_1-sum_(i=2)^4 a_i*v_i,

every G(x_v+j*a_1) for j<r is zero: its grid root has first coordinate
r-1-j. However

    G(x_v+r*a_1)=G(a_1-sum_(i=2)^4 a_i*v_i)

is nonzero over the symbolic field, because every displayed factor has
a_1 coefficient u_1+1 in {1,...,K}. Thus A_r(x_v)=0 at K^3 distinct
points and

    deg_X A_r >= K^3.

The same argument at x_v=-K*a_1-sum_(i=2)^4 a_i*v_i forces
deg_X A_0>=K^3 if A_0 is nonzero. The leading-endpoint bound alone
already applies to every nonzero relation of effective order <=K.

This is stronger than cancelling the first-order quotient: raising a
fixed order to another r<=K cannot replace the large face coefficient
by a bounded-degree endpoint. It does not handle r>K, rational coefficients
without charging their cleared numerator/denominator degrees, nonlinear
shifts, or a different computation of a single product value.

## Finite-field version with an explicit probability

Now choose a_1,...,a_4 independently uniform in F_p, and assume K>=1 and
16*K^4<=p. Define M=K^3 and boundary coordinates

    t_v=-sum_(i=2)^4 a_i*v_i.

Let B count boundary indices v for which G(a_1+t_v)=0.
For a fixed v each possible vanishing factor is the nonzero linear form

    a_1*(u_1+1)+sum_(i=2)^4 a_i*(u_i-v_i).

Its a_1 coefficient is nonzero mod p. By a union bound,

    E B <= M*K^4/p.

Let C count unordered pairs of distinct boundary indices with t_v=t_w.
Every such equality is also a nonzero linear equation in the slopes,
because K<p and v!=w. Consequently

    E C = M*(M-1)/(2p).

Among the indices not counted by B, the number of DISTINCT t_v values
is at least M-B-C. (The duplicate loss in each class is at most its
number of unordered pairs.) Therefore

    E[(B+C)/M] <= K^4/p+(M-1)/(2p)
                <= 1/16+1/(32K) <= 3/32.

Markov gives probability at least 13/16 that M-B-C>=M/2.
On this single event, SIMULTANEOUSLY FOR ALL orders 1<=r<=K,
each polynomial identity

    sum_(j=0)^r A_j(X)G(X+j*a_1)=0 in F_p[X]

with A_r nonzero has degree(A_r)>=M/2. Indeed the other terms vanish
at x_v=t_v-(r-1)a_1, and the r-th value equals G(a_1+t_v).
The good indices and their distinctness do not depend on r, so no
union bound over r is needed. Interpret the integer degree bound as
degree >= ceil(M/2).

This is about polynomial identities, not merely agreement on sampled
points. For a relation modulo N, its endpoint may reduce to the zero
polynomial modulo p; then this local degree conclusion does not apply
there. A proper coefficient-content gcd can itself supply a factor,
but finding and producing such a relation still costs work.

## Scope of the obstruction and constructive response

The event bound rejects a proposed universal low-order, low-degree
recurrence formula for the random-grid family. It does NOT show that
exceptional slopes are too rare to exploit: an upper bound of 3/16 on
the complementary event is not a vanishing probability or a full
expected-complexity lower bound. A strategy selecting exceptional slopes
needs its actual selector, distribution and rejection costs.

Likewise, a high polynomial degree is not the cost of every possible
compact coefficient circuit. The earlier block evaluator costs only
K^2 despite this face-degree count. Apply the deduction only to recurrence
algorithms that materialize or charge the actual endpoint polynomial
data according to their theorem hypotheses.

Two genuinely different computations remain outside the argument:
(1) a direct scalar product method using the compact grid without these
low-order shift coefficients; (2) an explicit method obtaining exceptional
local short relations among the slopes and extracting a proper gcd.
The latter cannot assume the unknown prime modulus or a short-vector
oracle for its index-p lattice.

The next audit should verify this boundary evaluation and finite-field
count before using it to close a recurrence family. No empirical screen
can replace that check, and no new broader review is launched merely
to duplicate the currently live affine-grid task.

