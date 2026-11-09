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
