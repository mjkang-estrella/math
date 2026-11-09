# Frozen review assignment

The scope and obligations below transcribe the user assignment. The two mathematical briefs are frozen from the matching repository files; this is not a raw conversation export.

Act as the review sub-agent for this task.

Work only /home/mj-kang/Documents/Dev/math/factoring-research. Read AGENTS.md RESEARCH_TEAM.md RESEARCH_LOOP.md README docs/SPECIFICATION. No recursive delegation, numerical parameter/prime/depth sweeps, candidate runs, shared solver/Lean/state edits, packages, commits or publication. Own ONLY research/findings/W012-cap-width-review* files. Freeze inputs and sources with delivery manifest. Exact fixed algebraic certificates permitted. Parent continues independent research; A is auditing the initial affine/convex query and B the primary hull literature, so do not duplicate those broad tasks.

## Full original W012 brief

# W012 — correlated certificates and convex interval exclusion

2026-10-08. Parent constructive wave; PROVISIONAL. No factoring complexity
improvement, numerical candidate experiment, installed solver or Lean change.
The previous W011 pilot failed its frozen finite screen. This wave changes
starting point: explicit arithmetic constraints and convex integer optimization,
rather than smooth relations or concentrating finite-field maps.

## Card A: two quotient certificates form an exact affine lattice

Let gcd(N,m)=1 and j be a unit modulo m. Define the rank-two lattice

    Lambda_j = {(u,t) in Z^2 : u*j^2 = N*t (mod m)}.

It has determinant m. Choose an oriented integer basis (u1,t1),(u2,t2)
with u1*t2-u2*t1=m; HNF and unimodular basis reduction are payable.
For each row choose v_i satisfying

    u_i*j^2+v_i*j+N*t_i = 0 (mod m^2),
    v_i+2u_i*j = 0 (mod m).                              (1)

The first equation uniquely determines v_i modulo m^2 and the second
then follows from membership in Lambda_j. Representatives may be shifted
by multiples of m^2 to center an eventual quotient. No factor is used.

For a true factor pair P*Q=N with P=j mod m, (1) implies

    i_i=(u_i*P+v_i+t_i*Q)/m^2 is an integer.               (2)

The reason is that u_i*P^2+v_i*P+N*t_i vanishes modulo m^2
by its value and derivative at j, and P is a unit modulo m^2.
Conversely, (2) can be inverted WITHOUT enumerating modular inverses:

    P = m*(t2*i1-t1*i2) -(t2*v1-t1*v2)/m,
    Q = m*(-u2*i1+u1*i2)+(u2*v1-u1*v2)/m.                (3)

The displayed constants are integers. The linear part has determinant
m^3. The proposed exact image is

    L_j = {(P,Q) in Z^2:
           P=j mod m, Q=N*j^(-1) mod m, P*Q=N mod m^2}.   (4)

Although the last condition is written quadratically, after fixing the
two mod-m residues its remaining mod-m^2 condition is linear; L_j is one
affine lattice of determinant m^3. To prove equality, show (3) lies in
(4) and both have the same determinant, or invert on each member of (4).
This is an exact correlated constraint, not separate marginal filters.

What work it might replace: simultaneous use of two useful quotient
certificates could conceivably replace a one-index collision table by a
small geometric search. The immediate danger is explicit: every integer
pair (i1,i2) already corresponds to a member of L_j. There is no remaining
free modulus sieve on those indices. Factoring still imposes the conic

    P(i1,i2)*Q(i1,i2)=N.                                 (5)

A small final answer set does not make this conic cheap to solve.
Scanning a K-by-K quotient box costs K^2 per j. With the existing
optimistic K~sqrt(N)/m^(3/2), doing that for all unit j costs
phi(m)*N/m^3, which is worse than the priced one-index collision search.
The alternative below uses a paid polynomial-time convex primitive
rather than assuming an integer-conic oracle.

## Card B: exact support queries certify factor-free intervals

For an integer factor interval [L,U] inside [2,floor(sqrt(N))], consider
the bounded convex set

    C = {(x,y): L<=x<=U, 1<=y<=N, x*y>=N}.

Its convexity follows from y>=N/x on x>0. For positive integers a,b,
compute exactly

    s = min {a*x+b*y : (x,y) in C intersect Z^2}.         (6)

The same query can be restricted to L_j by substituting the affine
integer coordinates (3); preimages under an invertible affine map remain
convex and degree two. All coefficient lengths and objective bit lengths
must be counted. A fixed-dimension convex semialgebraic integer optimizer
is a known candidate implementation of the query, not a unit-cost oracle.

For every factor P in the queried interval/lattice,

    a*P^2-s*P+b*N >= 0.                                  (7)

Therefore the OPEN real interval where a*X^2-s*X+b*N<0 is certified
factor-free. Its integer endpoints are computable with integer square
roots and exact comparisons. Boundary equality is not excluded: solve
the quadratic and verify any integer factor there. Also check any
returned optimizer x by gcd(x,N); a proper gcd is usable even if x*y>N.

One complete N-only baseline rule is:
* keep a queue of unexplored integer intervals, initially [2,isqrt(N)];
* take a midpoint h, test gcd(h,N), and if no factor choose
  a=N/g, b=h^2/g, g=gcd(N,h^2);
* ask (6), test its returned coordinate, remove the strict exclusion
  interval given by (7), test boundary factor candidates, then recurse
  on the remaining integer subintervals.

If h is not a factor, the real tangent at h has no integer minimizer
attaining its continuous value. Thus s>a*h+b*N/h, so h is strictly in
the removed interval. Every unsuccessful query removes at least one
candidate integer and termination follows. Even factors, squares,
primality and complete recursion need their ordinary preprocessing in
an all-composite implementation. The rule as written supplies only a
very conservative O(sqrt(N))*poly(log N) bound, not an improvement.

What could improve the complete cost: Q_N paid queries covering the
remaining factor range would cost Q_N*poly(log N), with no relation
collection or group-order preparation. An exponent improvement over the
checked deterministic 1/5 reference would require a proved query bound
below N^(1/5) (with the polynomial factors and preprocessing paid).
A polylogarithmic query bound would be much stronger and is not assumed.
Lattice-restricted variants must add every tested j and charge discovery
of any useful subset; the true residue is not given.

The decisive mathematical issue is query count and certified gap width,
not convexity or the existence of a optimizer. Do not use fixed-dimension
convex optimization directly on equality (5): its feasible set is not
convex. A promised composite does not repair that application.

## Card C: navigate the normal intervals instead of querying every x

A factor point (P,N/P) uniquely minimizes the real objective
lambda*x+y at lambda=N/P^2. It is consequently an exposed vertex of
the relevant integer hull. If a known hull vertex (x,y) has x*y>N,
every slope in its open normal interval corresponds to a tangent point
that cannot be a factor. Two certified adjacent vertices determine this
interval and therefore a whole factor-free x range. Endpoints need
separate treatment because an edge can tie several lattice points.

This suggests navigation by blocks of supporting slopes. It is a real
alternative to testing every trial divisor, but is not new machinery:
Alcantara, Blanco, Criado and Santos (2025), Corollary 1.2, give between
2*N^(1/3)-2 and O(N^(1/3)log N) vertices for the full standard hull.
Theorems 1.3/1.5 give next-vertex arithmetic algorithms, and Proposition
1.7 allows a start at a prescribed coordinate. Full enumeration already
gives a known factoring algorithm, not the desired gain.

Primary sources opened:
* https://arxiv.org/html/2501.19193v1 — introduction, precise Theorems
  1.1/1.3/1.5, Corollary 1.2 and Proposition 1.7 inspected by parent.
  Do not replace arithmetic-operation bounds by unit-cost bit bounds.
* https://link.springer.com/content/pdf/10.1007/PL00009496.pdf —
  Khachiyan–Porkolab; abstract and theorem scope require full audit.
* https://arxiv.org/html/2512.19076v1 — rank-three factoring framework,
  technical overview inspected; two certificates here are not two free
  independent factor relations or a claim to improve that preprint.

Under (3), the homogeneous quadratic part of P*Q has discriminant
sqrt(B^2-4*A*C)=m^3. The center is the inverse image of (0,0), so the
right-side hyperbola parameter is still N. A possible application of
the 2025 full-hull lower bound would give >=2*N^(1/3)/m-2 vertices per
residue, with the caveats of its hypotheses and all-input coefficient
sizes to be audited. Its upper bound has a second term involving the
discriminant; merely substituting N/m^3 in every bound is invalid.

MOST IMPORTANT SCOPE LIMIT: the source's lower bound is for the full
hull, with its proof using the first N^(1/3) lattice lines near the
asymptotes in the standard case. It is NOT a lower bound on a balanced
central arc, on an early-stopped factor search, or on adaptive support
queries. After a paid small-factor stage, those are exactly the cases
that matter. Do not close this branch using the wrong output-size bound.

## Selection and next decisive work

Select Card B with the exact lattice from A for symbolic/cost audit;
use C's primary results to price navigation and identify what remains.
Independent reviewers should check the affine bijection, complete
interval-exclusion algorithm, primary optimization theorem, and the
precise full-hull versus clipped/target-search scopes. No parameter or
prime sweep is preregistered. Fixed symbolic examples/counterexamples
may be checked exactly; no performance run should start from this note.

Parent work continues on certifying large gaps or sharing many support
queries. Simply renaming the missing selector as an oracle, reporting
the full-hull algorithm as new, or inferring a query bound from a tiny
set of actual factors would not advance this construction.

## New parent derivation

# W012 — a width bound for convex exclusion certificates

2026-10-08. Parent derivation, PROVISIONAL pending independent audit.
No numerical experiment. This concerns the information carried by one
empty convex cap, not all factoring algorithms or early-stopped searches.

## A concrete geometric obstruction

Fix integers R>=2, N>=R^2 and a residue chart m with m^2<=R.
Consider the affine lattice L_j from W012 (4), with unit j modulo m.
At every integer x=j mod m, its allowed y values form one progression
of step m^2. This follows either from the linearized product condition
or from the exact inverse-certificate construction.

Take an interval [u,v] contained in [R,2R], of width W=v-u.
Any convex set containing its whole hyperbola arc
{(x,N/x):u<=x<=v} contains the region between that arc and its chord.
At an x in [u,v], the chord's vertical height above the arc is exactly

    H(x)=N*(x-u)*(v-x)/(u*v*x).                           (1)

Choose x=j mod m nearest the midpoint; its distance from the midpoint
is at most m/2. If W>=m, this x lies in [u,v] and

    (x-u)*(v-x) >= (W^2-m^2)/4,
    u*v*x <= 8R^3,
    H(x) >= N*(W^2-m^2)/(32R^3).                         (2)

There is an allowed lattice ordinate y in [N/x,N/x+m^2).
The assumed m^2<=R and N>=R^2 ensure y<=N for R>=2, so it is inside
W012's vertical box as well. If the final lower bound in (2) is
strictly greater than m^2, this lattice point lies strictly below the
chord and above or on the hyperbola. It must belong to the convex hull
of the arc. Consequently a convex cap which contains this arc and no
allowed lattice point cannot have

    W > m*sqrt(1+32R^3/N) <= m*sqrt(1+32R).               (3)

Endpoint equalities and W<m are harmless: use a strict inner interval
and pass to its supremum, or retain a weak final bound.

For W012's support query, the region
N/x<=y<(s-a*x)/b over its strict factor-exclusion interval is empty of
allowed lattice points by optimality. Every closed subarc lying inside
that interval, and its chord, lie strictly below the support line.
Thus (3) applies to each connected exclusion interval, even if its
original quadratic endpoints are outside [R,2R]; first intersect and
take inner subintervals. This argument does not require estimating the
gap between the continuous optimum and the lattice optimum.

## What the bound prices

At most

    W/m+1 <= sqrt(1+32R^3/N)+1 = O(sqrt(R))

integers of a particular residue class can be removed by one such
support certificate in the balanced range. A constant number of
endpoint and coordinate tests per query changes only the constant.
Covering every retained candidate integer in [R,2R] across all unit
residues therefore requires, for m^2<=R, at least

    Omega(sqrt(R)*phi(m)/m)

queries, apart from absolute constants/boundary terms. With R on the
scale sqrt(N), this is an N^(1/4) scale up to the residue density.
This is a covering requirement; it is not a bound on finding one factor.
For m>sqrt(R), enumerating every unit residue already costs phi(m),
again of that exponent scale up to subpower density factors.

Even if a prior sieve removed every composite candidate, a cover of all
primes in [R,2R] coprime to m would have the elementary counting barrier
Omega(sqrt(R)/log R): there are order R/log R such primes for large R,
and each certificate removes only O(sqrt(R)) integer abscissas. This
optional prime-count specialization requires its standard primary
prime-distribution input; the integer covering bound above is standalone.

No factor-search lower bound follows: the algorithm may find a factor
early, use other information, omit charts by a new theorem, or represent
many exclusions implicitly. Nor does the full-hull vertex lower bound
prove (3); this is an independent cap calculation in a clipped central
range. One support optimizer can in principle be queried for other
information beyond this certificate. Such additional use needs a
specified algorithm and cost, not the same bound asserted universally.

## Constructive question after this obstruction

The useful primitive is real: one paid convex optimization can skip
several divisors with an exact certificate. But complete coverage using
separate connected empty caps cannot reach the target exponent below
1/5. A revised mechanism must change the amount of information per
paid computation: share a whole collection of caps without outputting
each one, use nonconvex arithmetic structure with a priced algorithm,
or supply a factor-selective navigation guarantee which avoids complete
coverage. Merely choosing better tangent slopes does not evade (3).

This does not select a numerical experiment. The next cheap test is a
symbolic audit of (1)-(3), the affine-lattice ordinate step, candidate
count and the strict coverage-versus-stopping distinction.

## Requested review

No prior reviews of this new derivation. Audit the chord identity, lattice ordinate period m^2, nearest residue abscissa, vertical box, strict versus closed cap, clipped interval width and integer covering count, including boundary constants. The intended novel scope is central-arc *covering by connected empty convex caps*, not all hull vertices or early-stopped factor search. Check whether a constant number of isolated tests per query or m>sqrt(R) invalidate the stated scope. The optional prime-count corollary may be omitted/qualified unless a primary source justifies it; do not blur composite preprocessing with the integer counting result. Seek a precise counterexample if wrong, or the sharpest valid proposition if right. No performance experiment authorized. Return complete proof/corrections and concise computational implication, not a general factoring lower bound.
