# W013 — cycles of residuals and direct divisibility-event extraction

2026-10-08. Parent constructive wave. Both cards bypass a large smoothness
relation matrix. Neither has an improved complete factoring bound. These are
proof-first constructions; no parameter sweep or performance run is selected.
The separate W012 square-selector audit continues without blocking this work.

## A. Replace smoothness by labelled residual cycles

For a positive unit a modulo N, the square-coordinate construction produces

    b=a*t^2-N,       b/a=t^2 (mod N).

On a path, maintain a_i=a_0*R_i^2 (mod N), with R updated by multiplying t.
If the path returns to a previously seen positive unit a, the quotient of
the two labels squares to 1. Test both signs by gcd with N. This directly
consumes a collision; no factorization of residuals, parity matrix or square
assembly over a prime base is required. A cycle can still give only +/-1.

The literal ceil-square map does not maintain small residuals:

    b < 2*sqrt(N*a)+a.

The size-envelope exponent beta changes to (1+beta)/2. Thus a proposed
small state universe cannot be justified by this bound; it rapidly approaches
N scale. This is an upper-envelope observation, not a typical-orbit theorem.

A materially different update divides the norm before repeating. Carry an
integer P with P^2=N+a*b and nonzero signed a,b. At a gcd-clean step the
edge label is P/a modulo N, since b/a=(P/a)^2 modulo N. Select

    P'=P+k*b,       c=(P'^2-N)/b = a+2*k*P+k^2*b,

then move from a to b to c, updating labels. The division is exact by the
previous identity. Each step uses O(log N)-bit arithmetic if coefficients
are kept bounded. Choosing k to put P' near sqrt(N), and tracking signs,
is the starting point for a quadratic-form reduction, not an assumed new
algorithm or a proved bound on this particular rule.

There is an immediate exact obstruction to a naive cycle-count argument.
Choosing P'=P gives c=a, but the two labels multiply to

    (P/a)*(P/b)=P^2/(a*b)=1 (mod N).

Choosing P'=-P instead gives -1. Every immediate reverse edge is therefore
trivial. A useful cycle needs sign information that does not telescope in
this way. Counting returns of a alone is not a success-probability proof.
All gcd failures, zero states, signed representatives and label inversions
must be handled explicitly.

The family is visibly related to continued fractions and reduced binary
quadratic forms. The parent read only the introduction and background of
Gower--Wagstaff, *Square Form Factorization*, author-hosted primary PDF:
https://homes.cerias.purdue.edu/~ssw/squfof.pdf . That source explicitly
uses assumptions on principal-cycle walks in its complexity analysis.
An independent review must identify the exact overlap before any novelty
or birthday bound is adopted.

Cheap rejection sampling is not a substitute for a reduction. For an odd
distinct semiprime, draw R uniformly among units and retain R^2 mod N in a
set S containing M unit squares. Acceptance is exactly 4M/phi(N), and the
retained values are uniform on those M squares. An independent birthday
collision needs order sqrt(M) accepted values (for M growing); each has
four equally likely root labels, and a collision has mixed-sign probability
1/2. Acquiring that collision costs order phi(N)/sqrt(M) raw unit samples,
before gcd/inversion overhead. This remains at least order sqrt(phi(N))
because M<=phi(N)/4. A smaller retained range makes this sampler worse.
Early nonunit gcd successes are additional events, not omitted for an
all-algorithm lower bound. This is only a cost for the stated clean sampler.

The decisive audit is therefore the concrete divided-norm update: distinguish
known form reduction, trivial backtracking and an actually mixed useful cycle.
No claim of independent uniform reduced coefficients, free small roots or
polylogarithmic cycle mixing is supplied. A useful revision must price a
non-backtracking generator with useful label collisions, rather than merely
asserting a small support. This card is not selected for a timed screen.

## B. Detect divisibility events through a polynomial residue filter

For an integer x>=1,

    floor(N/x)-floor((N-1)/x) = 1 exactly when x divides N.

Thus finding one nonzero event on [2,isqrt(N)] factors directly. Ordinary
floor summation alone is not assumed fast. The proposed computation is a
shared modular filter for a whole block x=X+h, 0<=h<H, X>=2.

Fix a constant degree d. Let

    c_j=(-1)^j*N/X^(j+1),   A(h)=sum_(j=0)^d a_j*h^j,

where a_j are integers approximating q*c_j for one positive denominator q.
The reciprocal Taylor remainder is EXACTLY

    N/(X+h)-sum c_j*h^j
      = (-1)^(d+1)*N*h^(d+1)/(X^(d+1)*(X+h)).          (1)

If |q*c_j-a_j|<=eta_j, a certified uniform error is

    E=sum eta_j*H^j + q*N*H^(d+1)/X^(d+2).            (2)

For a factor x=X+h, q*N/x is an integer multiple of q. Consequently

    A(h)=e (mod q) for an integer e with |e|<=floor(E). (3)

An executable block routine constructs q and the a_j; computes a rational
upper bound E; enumerates all roots of A(h)-e modulo q for every permitted
e; lifts them into [0,H); and tests those x by exact division/gcd. It cannot
miss a factor if the error bound and root enumeration are correct. If q is
prime and A is nonconstant modulo q, at most d roots occur per e. If also
q>=H and E=O_d(1), the block needs only O_d(1) final candidate tests.
Composite moduli, degenerate polynomials, acquiring/factoring q, repeated
residues and the whole root algorithm are paid. No modular root oracle is
included in the proposal.

The attractive CONDITIONAL scale was q~H, constant E, X~sqrt(N). The Taylor
term permits H=N^(d/(2d+4)), suggesting N^(1/(d+2)) balanced blocks. Degree
four would then suggest N^(1/6) blocks. This counts neither denominator
acquisition nor roots and is not a factoring bound. The following elementary
calculation specifically rejects its coefficientwise short-denominator gate.

### The missing high-degree information disappears at a short denominator

Work on a balanced block with X^2<=N<=4X^2, H>=2 and d>=2. Suppose q*4/X<1/2
and the proposed sufficient approximation has

    |q*c_2-a_2| <= 1/H^2.

Here c_2=N/X^3 is positive, between 1/X and 4/X. Since 0<q*c_2<1/2 and
1/H^2<=1/4, the only possible integer a_2 is 0. Therefore necessarily

    q*N*H^2 <= X^3, hence q*H^2<=X.                  (4)

In particular q>=H forces H^3<=X. The putative d=4 block size H~N^(1/3)
with q~H fails this necessary condition on every sufficiently large balanced
block, not merely on an unlucky input family. Already degree two carries
curvature of size 1/X, which such a short common denominator rounds to zero.
Higher degree does not fix that lost coefficient.

This rejects the specified coefficientwise sufficient gate, not all uniform
polynomial approximations: their errors can cancel. Nor does it lower-bound
all variable moduli, multiple representations, shared root computations or
factoring algorithms. Even a successful denominator must still be acquired,
and factoring a denominator is not free just because it is smaller than N.

Weighted simultaneous Dirichlet approximation also exposes the cost: to
guarantee ||q*c_j||<=H^(-j) for all j=1,...,d by the pigeonhole construction,
one only obtains q<=H^(d(d+1)/2). It neither guarantees q>=H nor a prime or
smooth q. With that budget, keeping the Taylor term constant permits at
best H~N^(d/((d+1)*(d+2))). Ignoring every other cost, the corresponding
balanced block count is N^(1/2-d/((d+1)*(d+2))); d=1 and d=2 give 1/3,
and d>=3 gives a worse exponent. These are budgets of this construction,
not a lower bound on special correlated Taylor coefficients.

### Constructive next question

The exact event filter (1)-(3) is useful, but short denominators cannot
retain its proposed high-degree Taylor data through the given acquisition
rule. A materially different computation would have to process many target
residues e in (3) together, or exploit the exact rational denominator X+h
without expanding into a large common denominator. The latter is precisely
where a paid variable-modulus algorithm is needed; restating divisibility
as an oracle is not progress. No such fast primitive is claimed here.

Independent review is requested for the exact filter, the obstruction (4),
and the budget comparison. Check narrow prior art around Sladkey's geometric
divisor-sum method (arXiv:1206.3369) and deterministic factoring interval
methods before calling the filter new. Do not search numerical parameters
for a gate that already has the stated algebraic obstruction.

### Stronger degree-four obstruction, allowing cancellation of errors

The parent can remove the coefficientwise restriction for the actual selected
degree-four construction. Let X^2<=N<=4X^2, 10<=H<=X, m=floor((H-1)/4),
0<q<X/240. Suppose an integer-coefficient polynomial A of degree at most
four satisfies

    |A(h)-q*N/(X+h)|<=E for all integer 0<=h<H,
    (40/3)*E/m^2 < 1/4.                              (5)

Interpolate F(h)=q*N/(X+h) at h=0,m,2m,3m,4m by I(h). Its exact Newton
formula is

    I(h)=sum_(k=0)^4
       (-1)^k*q*N*prod_(j=0)^(k-1)(h-j*m)
       / prod_(j=0)^k(X+j*m).

The coefficient alpha of h^2 is positive. The k=2,3,4 terms contribute
numerators 1, 3m, 11m^2 respectively, hence

    q/(6X) <= q*N/[X*(X+m)*(X+2m)] <= alpha
      <= 15*q*N/X^3 <= 60*q/X < 1/4.                (6)

The deliberately loose lower bound uses N>=X^2 and m<=X. For the upper
bound each denominator is at least X^(k+1), and m<=X.

On nodes z=0,1,2,3,4 the coefficients of z^2 in the Lagrange basis are

    35/24, -13/3, 19/4, -7/3, 11/24.

Their absolute sum is 40/3. Interpolating A-I from its five errors, each
bounded by E, gives

    |a_2-alpha| <= (40/3)*E/m^2 < 1/4.

Since a_2 is an integer and 0<alpha<1/4, necessarily a_2=0. Combining
with (6) yields q*m^2<=80*E*X. Since H>=10 gives m>=H/8,

    q*H^2 <= 5120*E*X.                               (7)

Thus if q>=H and E is bounded, the block width is at most O(X^(1/3))
even when arbitrary cancellations among all four approximation errors
are allowed. This closes the selected uniform degree-four residue filter
at q~H as a way to process balanced blocks of size N^(1/3). It does not
depend on the Taylor remainder being small or on a special N family.

The restriction is to one integer-coefficient degree-four A that uniformly
approximates the real reciprocal after scaling by q. A filter which is
only locally close modulo q, uses a changing denominator, higher growing
degree, or implicitly batches many target residues is outside the proof.
Such a changed computation needs an explicit algorithm and total cost.
This is a parent proof pending independent review, not a Lean theorem.

## Disposition and diversity

B is the deeper computation in this wave: it specifies a finite block filter
and resolves a hidden denominator assumption symbolically. Its hoped-for
degree-four gain is rejected provisionally pending audit. A remains a
separate cycle/extraction question with a known-method warning. W012 D audits
the relation-selection branch. No shared solver or Lean expansion is selected
for these nonsurviving complexity proposals, and no all-input success theorem
or new asymptotic improvement is claimed.
