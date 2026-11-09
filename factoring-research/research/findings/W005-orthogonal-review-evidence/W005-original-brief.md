# W005 — Parent-led mechanisms, validation delegated

Date: 2026-10-08. Status: active constructive research; all new deductions below
are **PROVISIONAL**, pending independent review. Verified new complete
factoring improvement: **NONE**.

## Operating mode

The user explicitly asks the main thread to sustain independent brainstorming,
with T3 children handling correctness, complexity, prior art, counterexamples
and bounded experiments. A pending review blocks acceptance of its claim, not
other ideation. Preserve all previous task handles. Keep a small diverse set;
record saved computation, acquisition cost, success law and a decisive test.
No report count is a progress measure. Work only inside factoring-research.

This wave is symbolic first. Do not execute a candidate or numerical search
merely because a diagnostic is mentioned. A child proposing an experiment must
first freeze its precise primitive, corpus, controls, budgets and rejection
criterion in its exclusive prefix. A full algorithm benchmark must use the
existing research harness. No package, shared-code, Lean or scheduler changes
are authorized by this brief. Parent owns shared state and registries.

## A. Construct the point before fixing the second trace — lead direction

**Saved work sought:** replace a search for the first nontrivial rational point
on a fixed quartic by an explicit rational section, then generate candidates
by its elliptic group law. This is a primitive proposal, not a root-supply claim.
It changes which object is selected first; it does not assume a point oracle.

Start from W004's accepted first field f(T)=T^2-s*T+t^2, t=2R,
Delta=s^2-4t^2 positive nonsquare, and s=5R mod N. In W004, the second
trace s_j was fixed before searching
W^2=f(X)*f(s_j-X). Set b=s_j-s, z=X-s_j/2 and
a=f(s_j/2), c=2a-b^2. Direct expansion gives

    W^2=z^4+c*z^2+a^2,
    c+2a=-Delta, c-2a=-b^2.

The explicit cubic is

    E_b: y^2=x*(x+b^2)*(x+Delta),
    x=2*(W+z^2)+c, y=2*z*x,
    z=y/(2*x), W=(x-c)/2-z^2.

Require b, Delta, Delta-b^2 nonzero. The two infinity points and two
midpoint points z=0,W=+/-a map to the identity and the three 2-torsion
points. Thus group operations on only those four obvious points cannot supply
new candidates. This is a claim about that generating set, not the rank.

**Actual new point construction:** choose rational r != 0,+/-1, put

    b=t*(r-1/r), w=t*(r+1/r),
    x_P=4t^2, y_P=2*t*s*w.

Because b^2+4t^2=w^2 and Delta+4t^2=s^2, P lies on E_b.
Choose r in the localization Z_(N), with r and its denominator units and
r=1 mod N. Then b=0 mod N, so the new rational trace s_j=s+b still has
the required modular value. A concrete eligible choice is
K=N*s^2+1 and r=1+N/K: both K and K+N are units modulo N and r is close
to 1. Check every other denominator before modular reduction. The parent
follow-up below identifies a valuation obstruction for this literal choice;
eligibility of r does not imply eligibility of the square lifts.

The section is not asserted nontorsion without proof. It visibly differs from
the four 2-torsion points, but finite torsion and degeneration must be checked.
Scalar multiplication on rational points also grows height; O(log k) group
operations is not an O(log k) bit-time claim for [k]P.

**Lift diagnostic, already explicit:** inverse substitution yields

    X = ((s+2t)*r + (s-2t)/r + 2s)/4,
    s_j-X = (-(s-2t)*r -(s+2t)/r + 2s)/4.

Their being rational squares is not automatic. Even that only reaches the
rotation norm cover, not its ordinary-square field target. For r>1, the second
quantity is positive only for r < (s+2t)/(s-2t); check endpoints and signs.
The old integer sum-of-two-squares anchor and second-field distinctness must
be reconstructed, not inherited for rational s_j.

**Important alternative-use gate:** when b=0 mod N, E_b reduces at every
unknown p|N to y^2=x^2*(x+9R^2), with node (0,0). Its invariants are

    c4=16*(b^4-b^2*Delta+Delta^2),
    D_E=16*b^4*Delta^2*(b^2-Delta)^2.

c4 is a p-unit while D_E is not, so the j-invariant has negative p-adic
valuation. This is intrinsic bad reduction. On the smooth locus, put
q=y/x, kappa=3R, lambda=(q+kappa)/(q-kappa); infinity maps to 1.
The chord law identifies this locus with F_p^*, not a generic good-reduction
elliptic group. Therefore ordinary ECM curve-order randomness cannot be
imported here. Points reducing to the singular locus need separate treatment.

**Decisive questions:** is this an infinite-order section, and can a
deterministic rational-point sequence supply both square lifts at useful
total cost? First seek algebraic factorization of these two square conditions;
if they encode a root of R or force a new high-genus search, isolate that
obstruction precisely. Construct a replacement computation, not just a new
name for the missing point finder.

## B. Direct splitting from quaternion orientations

**Saved work sought:** avoid smooth relations and order finding. Obtain
primitive integer/Hurwitz quaternions Q_1,Q_2 of norm N, then run the
Euclidean right-gcd algorithm; a gcd with norm strictly between 1 and N
would split N. Charge the norm-N sampler and all divisions. No fast sampler
has been supplied here; source it exactly or keep its cost explicit.

For N=p*q, an idealized uniform local orientation is a line in P^1(F_p).
Two independent right ideals match with probability 1/(p+1), suggesting
birthday rather than polynomial supply. Do not assume a concrete sampler
has this distribution.

**Specific correlation attempt:** generate Q_2 by a rational Householder
reflection of Q_1 in a short integer vector w,

    Q_2=Q_1-2*<w,Q_1>*w/||w||^2.

Check gcd(||w||^2,N) first. A proper gcd already factors N; a nonunit
denominator cannot be used. Clearing a unit denominator preserves the local
orientation. This is an explicit finite transformation, not an ideal sampler.

**Parent's prospective falsifier:** modulo p, a nonzero dot product makes
Q_2-Q_1 an invertible quaternion, since w has unit norm. Therefore Q_1 and
Q_2 cannot have a common nonzero right kernel. If the dot product is zero,
Q_2=Q_1 there. Thus the p component of the right gcd may encode exactly
the already available scalar gcd(<w,Q_1>,N). Check handedness, primitive
hypotheses, repeated primes and Hurwitz denominators rigorously. More
generally, a shared kernel makes det(Q_1-Q_2)=0, so any claimed quaternion
gain must be compared with the scalar norm of that difference.

**Constructive escape question:** can correlated quaternion generation make
that scalar gcd useful with less work than directly searching the scalar
form? Short-vector reduction that merely makes a nonzero scalar smaller
than the hidden prime rules out its divisibility, rather than amplifying it.
A changed generator must exhibit its scalar-form distribution and full cost.
This direction uses noncommutative geometry, independently of A's field roots.

## C. Thin-strip divisor search with exact floor-sum pruning

**Saved work sought:** locate an integer point on x*y=N without constructing
a product over all candidate divisors or collecting square relations.

A fully specified starting algorithm processes integer intervals [a,b] in
[2,floor(sqrt(N))]. On each interval enclose the lower curve (N-1)/x
by its tangent at a and the upper curve N/x by its secant through a,b.
Convexity puts every point in the exact divisor strip

    (N-1)/x < y <= N/x

inside this rational linear wedge. Sum floor(U(x))-floor(L(x)) over
a<=x<=b using exact Euclidean floor_sum. The value counts integers satisfying
L(x)<y<=U(x), including a possible boundary divisor; no floating arithmetic.
If zero, discard the interval. If positive and a=b, test N mod a and return
a proper factor if present. Otherwise bisect at floor((a+b)/2), using
disjoint child intervals. Charge every node, coefficient width and floor_sum
step. Handle the a=b formula separately. Search order is fixed left first.

The tangible sharing mechanism is one exact arithmetic-progression count per
whole interval; a zero count removes all its trial divisions. It is not the
unspecified RootProduct primitive from earlier waves.

**First cost diagnostic:** tangent/secant vertical error has size
O(N*h^2/a^3) on intervals of width h small relative to a. Wedge area is
O(N*h^3/a^3)+O(h/a), suggesting h about a/N^(1/3) before a typical count
becomes small. This is a heuristic work diagnostic, not a theorem about the
actual integral positions. If this scale survives, the literal method is
slower than the verified deterministic N^(1/5) baseline.

**Material escape:** degree-d Taylor envelopes suggest fewer outer blocks,
but their interior count is no longer a linear floor_sum. Do not grant a
polynomial-strip counter for free. First prove the literal algorithm's finite
cost and determine whether correlated neighboring empty wedges permit a real
reuse of Euclidean states. A concrete update rule and measured/derived total
work are required before proposing such reuse.

**Cheap falsification:** a preregistered primitive screen may compare visited
nodes, total Euclidean steps and bit widths with straight trial division,
across balanced, unbalanced and near-square composites and prime controls.
Generation work and failures must be retained. No factors enter the solver.
It would test pruning work, not prove a new exponent or beat a production
factoring algorithm. Do not execute until the exact protocol is frozen.

## Selection and scope

A is selected for parent development because it already supplies a symbolic
point-generation formula absent from the fixed-curve attempt. That is a local
primitive advantage only; the remaining lifts can entirely erase it.
B is a direct algebraic escape candidate with a very cheap symbolic falsifier.
C is a distinct exact geometric search whose actual executable baseline is
clear, even if its first scaling estimate is unfavorable. Validation should
kill weak versions promptly and return the precise replacement computation
that would be needed. Do not broaden any negative conclusion to all factoring.
