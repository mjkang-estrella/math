# W032: remove the large-base event count by a two-dimensional cover

Parent constructive extension, 2026-10-08. **Accepted with the boundary convention below** in
W032-arrangement-cover-review.md. Its imported lift identity is now
accepted by the separate W032-lift-sweep-review.md. No experiment.
Verified complete factoring improvement: **NONE**. The separate frozen
three-input sweep diagnostic is unchanged; it still uses a0=1.

The one-parameter sweep uses O(R*a0+R^2) threshold records when the base
points are a_i=a0+i. Large a0 would make that literal sweep expensive.
The following concrete replacement visits a superset of all attained gcd
arguments, using rational line arrangements of polynomial size in R.
It does not assume a discrete-lattice feasibility oracle.

Use the notation and integer c0,b_i of W032-lift-breakpoint-sweep.md,
with 0<a0 and a0+m<N and all original base points units. For a parameter
w in [0,N), write a0*w=N*t+z with 0<=z<N. Since the signed binomial
weights sum to zero,

    c(w)=c0-sum_i w_i*floor((z+i*w+b_i)/N).             (1)

The large common term t cancels. Thus all true outputs are values of

    C(x,z)=c0-sum_i w_i*floor((z+i*x+b_i)/N)             (2)

on the square 0<=x,z<N. The actual orbit uses integer x=w and
z=[a0*w]_N. For a superset consumer, evaluate (2) on every open region
of the square cut by

    z+i*x=k*N-b_i,       i=0,...,m, k=1,...,i+1.        (3)

There are at most J=(m+1)(m+2)/2=O(R^2) lines. More distant integer
levels cannot meet the square because 0<=z+i*x+b_i<(i+2)N.
Coincident lines can be deduplicated; parallel lines are retained when
distinct. All coefficients are explicit and have O(logN+logR) bits.

Every integer point of the square, including a line intersection, has
the same floor vector as some open region. Perturb z upward slightly;
on every line through that point all floor arguments increase, matching
floor's value at its lower integer endpoint. Choose the perturbation
small enough not to cross any other line or the upper square boundary.
If x=0, then also increase x by a sufficiently small positive amount.
All i are nonnegative, so this additional perturbation preserves the
same direction at coincident boundaries. Actual integer points have at
least unit clearance from the excluded upper x=N,z=N boundaries.
Therefore testing all open-region values includes every actual c(w).

Values from regions with no actual orbit point are permitted EXTRA gcd
arguments. A reported factor must still satisfy 1<gcd(C,N)<N. Such a
factor is valid even if it was not the original filtered scalar's value
on any actual lift. Do not assign an actual w witness or claim an exact
uniform-lift success probability for these extra regions. Failure of
the whole superset certifies failure of the particular lift family.

## A literal polynomial-time enumeration

An optimized arrangement routine is unnecessary to make the mechanism
concrete. Form all x coordinates where two nonparallel lines in (3)
intersect inside the closed square, the z=0,N crossing coordinates of
nonhorizontal lines only, and the endpoints 0,N. For i=0 do no edge
division: retain interior horizontal lines for slab heights, and ignore
boundary-coincident lines as cuts (including i=0,b_0=0 at z=N). Keep only coordinates in [0,N],
sort and deduplicate them as exact rationals. There are O(J^2) cuts.

For each adjacent pair of distinct cuts, choose their rational midpoint
x*. Compute all line heights at x*, keep those strictly between 0 and N,
add heights 0,N, sort and deduplicate. In every adjacent height interval
choose its midpoint z* and evaluate (2) by exact integer/rational floors.
No sampled midpoint lies on any line. Every open region spans at least
one of these vertical slabs and is met by a sampled midpoint. Boundary
values needed for actual integer lifts were already covered by the
one-sided perturbation argument.

This intentionally simple algorithm visits O(J^3)=O(R^6) sample points,
with O(R) floor work per point, plus paid sorting and intersections.
It uses polynomial time in R and logN, conservatively soft
O(R^7*(logN+R)) bit work with fast integer arithmetic and gcds; a looser
polynomial envelope is sufficient here. This is not an optimized bound.
Intersection denominators divide nonzero slope differences of magnitude
at most m. Midpoints of two cuts have denominators O(m^2); height
midpoints add only a constant factor. All rational numerators/denominators
therefore have O(logN+logR) bits, rather than uncontrolled rational growth.
Weights/c0 have O(R) bits. Exact comparison uses paid cross-products.

The arrangement has O(J^2)=O(R^4) open regions, so there are at most that
many distinct floor vectors and distinct C values. Duplicate processing
in the slab implementation costs time and cannot be refunded. A seen-set
may avoid repeated gcds at its own storage cost, without changing coverage.
The base lower-polynomial acquisition, input checks and all failed gcd
outcomes are additional paid work as before.

## What this changes and what it does not

This eliminates the factor a0 in the event-count bound and allows a
genuinely public large or randomized base start without enumerating its
O(R*a0) slope crossings. It replaces exact orbit membership by a larger
explicit set of valid gcd arguments. It does NOT supply a factor-yield
law for that set or prove an end-to-end polynomial-time factoring bound.

For an optional magnitude check, put beta_i=b_i/N. Since
c0=Delta^m beta_i+Delta^m v_i/N^L from the base acquisition, equation (2)
and annihilation of z/N+i*x/N give

    C(x,z)=Delta^m v_i/N^L
            +sum_i w_i*frac(z/N+i*x/N+beta_i).

Both signed fractional sums are bounded by their positive/negative
weight totals, so |C(x,z)|<4^R*(1+1/N). This controls actual operand
width even for extra region values. It does not guarantee that any of
the polynomially many values is divisible by a large input prime.

The decisive audit is the exact common-slope cancellation, all boundary
cases in the open-region cover, complete rational slab enumeration and
cost. A future test must have a new preregistration, separate from the
already frozen one-dimensional diagnostic. No such test is run here.
