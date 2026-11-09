# W012 geometry disposition

2026-10-08. Parent read the complete A, B and C reports and checked every
delivery entry: A 19/19, B 20/20, C 14/14 matched SHA-256 and byte sizes.
Frozen submissions, including recorded subsequent input drift, remain the
review objects. Verified new complete factoring improvement: **NONE**.

## Accepted results

A's affine quotient bijection is correct, including signed representatives
and m=1. Its image has determinant m^3 and is exactly L_j; there is no
unspent independent congruence sieve. B correctly distinguishes this raw
discriminant from primitive normalization: content m^2, primitive
discriminant parameter m, centered right side N/m^2. The invariant ratio
is N/m^3; the sharper full-hull upper-bound parameter is max(2m,N/m^3).

A's domain-clipped support exclusion and midpoint baseline are accepted.
The fixed-dimensional convex-semialgebraic theorem prices the query in
polynomial bit time; it does not minimize the nonconvex equality or residual.
The query must preserve its own residue and interval scope. Exact strict
integer endpoints use isqrt(D-1); equality requires a separate factor test.
The baseline terminates in O(sqrt(N))*poly(log N) work. A's sharp
delta>=h bound and its infinite family with a one-integer first exclusion
are accepted. This disproves a uniform larger local progress guarantee,
not amortized progress or an early-stopped algorithm bound.

C's self-contained cap proof is accepted in its strengthened form. An
empty convex cap over [R,2R] has width at most
m*sqrt(1+32R^3/N), without requiring m^2<=R. For a fixed actual retained
population S, one chart cap removes at most

    D=min(floor(R/m)+1, ceil(sqrt(1+32R^3/N)))

candidate abscissas. With at most k isolated tests per query, complete
coverage requires Q>=ceil(|S|/(D+k)). Preprocessing changes |S| and is paid.
The balanced complete-integer-cover obstruction is Omega(N^(1/4)/log N)
in the stated small-modulus regime. It is a query-count lower bound, not
an optimizer bit-cost lower bound obtained by multiplying by an upper bound.

B's exposure and closed normal-cone exclusion are accepted. A factor point
is uniquely exposed at its tangent slope. A nonfactor vertex's CLOSED
normal interval contains no factor tangent, including its boundary slopes.
Two adjacent vertices give one slope; a vertex interval requires both
neighbours. This differs from A's objective-value quadratic boundaries.

B's primary-source scope is retained: ABCS proves full-hull bounds and
next-vertex/jump algorithms. A jump does not certify the skipped chain.
The paper already presents factoring by hull enumeration; no novelty is
claimed here. Costs quoted in arithmetic operations are not unit bit costs.
The paper's intermediate-bit-size remark was not audited by B.

## Scope corrections to the review conclusions

Do not promote B's phrase "the only route ... is localization" to a theorem
about all uses of support answers. Its argument concerns explicit walking
or individual cone certificates; implicit batch computations, different
statistics of answers and preprocessing require separate analysis. Nor does
the sufficient window N^(3/10) establish a necessary localization width.

The precise C4 count is vertices whose normal ranges INTERSECT the central
block. Their abscissas can lie just outside it. The report's later shorthand
that the block itself "contains" that count is not adopted literally.
No new research step depends on its sharper constants or C5's window bound.
C's independently proved finite covering formula is the authoritative
obstruction used in this checkpoint.

Visiting every unit residue costs phi(m) only for an implementation that
does so. When m exceeds the block length, some or all classes may be empty;
C's occupied-class correction applies. B's unqualified large-m enumeration
sentence is not a universal algorithm lower bound. A modulus beyond sqrt(N)
encodes a factor in its residue only under the stated smaller-factor promise.
The Coppersmith comparison is an unaudited pointer, not an accepted result
of this wave.

## Constructive consequence

Better isolated tangents alone do not remove the full-coverage bottleneck.
The independent parent navigation certificate already kills one simple
product descent. The current continuation instead consumes nearby products
as square relations: W012-square-coordinate-relations.md. Its exact normal
sampler law is under a new D audit, with all A/B/C handles preserved as
completed. A separate residual-cycle computation is being developed to test
whether one can avoid both smoothness and exhaustive interval coverage.

No shared algorithm or Lean theorem was added. None of these scoped
obstructions is a lower bound on integer factoring.
