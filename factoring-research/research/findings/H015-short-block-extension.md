# H015 extension — short runs cannot merge distant cofactor bands

Date: 2026-10-08. Parent-derived extension of the
[fixed-family screen](H015-geometric-family-bound.md). **Pending independent
review; verified factoring complexity improvement remains NONE.** This is an
analytic count, with no finite experiment, parameter sweep, or solver change.

The family key in H015 is too fine to bound every possible geometric grouping.
This extension permits different u and v families to merge, but only when the
actual integer giant exponents fit short consecutive runs of step m². It
explicitly excludes identifications using modular orders or different strides.

## Hypotheses and elementary capacity bound

Retain positive N,m, gcd(N,m)=1, H<=C*sqrt(N*m) for fixed C, and a common
whole cell [P,2P] with sqrt(N)/4<=P<=sqrt(N)/2. For every unit residue j,
choose one informative certificate covering that cell. It has

    |u| <= U := 48C*sqrt(m),    |t| <= T := 12C*sqrt(m),
    u*j² = N*t mod m.

For sufficiently large m, U,T<m. Neither u nor t can be zero: the displayed
congruence would force the other to be a multiple of m within these strict
bounds, contrary to informativeness.

Fix t and let g=gcd(t,m). Since N and j are units, every corresponding u
has gcd(u,m)=g. There are at most 2*floor(U/g) nonzero multiples of g in
[-U,U]. After division by g, its congruence is

    (u/g)*j² = N*(t/g) mod q,     q=m/g,

where both coefficients are units modulo q. A unit quadratic congruence has
at most 2 roots at each odd prime power and at most 4 at a power of 2.
Consequently it has at most

    R_m := 2^(omega(m)+1)

roots modulo q, including q=1 under this generous bound. Each such residue
lifts to at most g residues modulo m. Taking the union over u shows that
one t can serve at most

    2*(U/g)*g*R_m = 2U*R_m

unit j, regardless of v. Thus the number D of distinct t represented obeys

    D >= phi(m)/(96C*sqrt(m)*R_m) = m^(1/2-o(1)).           (1)

For completeness, the root bound at odd prime powers follows by comparing
any two roots x,y: the prime cannot divide both x-y and x+y because x,y
are units. At a power of 2 the same argument leaves at most the four
classes x=+/-y modulo the penultimate power. The Chinese remainder theorem
multiplies the counts. No roots or factorization of N are supplied to a solver.

The last equality in (1) is an asymptotic lower bound. It uses only
2^omega(m)=m^o(1) and phi(m)>=m/2^omega(m). The first follows from the
factorial lower bound on a product of omega(m) distinct primes, which gives
omega(m)=o(log m). No residue equidistribution assumption is needed.

## Centers lie in separated bands of integer exponents

Using the sharper same-cell coefficient bounds from H015,
|u|P<=12H and N|t|/P<=24H, evaluation at P gives |v|<=37H.
For P>=1, |u|<=12H also, so the actual giant exponent satisfies

    E=u+v+N*t ∈ [N*t-49H, N*t+49H].                       (2)

Assume additionally H<=N/196. This holds eventually when m=N^(1/5+o(1)).
The distance between any two bands with distinct integer t is at least
N-98H>=N/2. The sign of t causes no exception.

Consider a grouping into consecutive integer-exponent runs

    b, b+m², ..., b+(L-1)*m²,

with arbitrary integer starts b, each mapped to modular values by alpha^E
for the fixed unit alpha. This describes literal exponent equalities, not
equalities found by reducing an exponent modulo an unknown order.

A run containing representatives from two distinct t bands must have

    (L-1)*m² >= N/2,   hence L>=1+N/(2m²).                 (3)

If the total represented run length is below N/(2m²), no run can span two
bands. It follows that at least D=m^(1/2-o(1)) runs are necessary. For
m=N^(1/5+o(1)), this is N^(1/10-o(1)) runs. Bridging even one band gap by
filling every missing step instead costs at least N^(3/5-o(1)) represented
positions, compared with the m*poly(log N)=N^(1/5+o(1)) giant-step scale.

This is a precise dichotomy for the proposed representation: exponentially
many short runs, or a very large padded run. It is not a runtime lower bound
for a different compressed product representation that avoids materializing
or processing those positions.

## Scope and next obligation

Unlike the initial family count, (1) permits sharing across all u and v for
each fixed t. Equations (2)–(3) then control merging different t by short
runs with the actual stride gamma=alpha^(m²). This rules out the specific
hope of polynomially many short literal-exponent runs covering all unit
residues on the common cell, if the proof survives review.

It does not bound the number of distinct modular values, arithmetic
progressions with other strides, relations between different bases, sparse
exponent-set evaluators, or algorithms that avoid the per-residue whole-cell
coverage obligation. Equality modulo N can identify distant exponent bands
through the order of alpha. Exploiting such identifications still needs a
costed method; the count does not prove that method impossible.

The separate H012 full-range cover obstruction is under independent review.
This extension neither depends on that proof nor supplies its missing review.
Before using this stronger cross-family conclusion to close a proposed
algorithm, independently check (1), both envelope constants, and the literal
exponent/run-length boundary. A new batching algorithm must explain which
of these stated assumptions it escapes and pay for doing so.
