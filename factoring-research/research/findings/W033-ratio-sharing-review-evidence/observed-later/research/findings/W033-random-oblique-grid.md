# W033: an explicit random oblique grid and the cost of sharing trials

Parent derivation, 2026-10-08. **Not independently accepted.** No numerical
run. Verified complete factoring improvement: **NONE**. This supplies a
different actual generator after the axis-aligned CRT construction paid for
whole prime-group products.

For a size parameter H, sample a uniform unit u modulo N with paid unit
testing. Set

    S_u={i*u modN:1<=i<=H},   T={j modN:1<=j<=H}.

Use the separating collision consumer to look for a proper gcd of i*u-j.
There is no prime table, CRT coefficient construction, or enormous input
integer. Initial nonunit samples are ordinary factor exits. For the analysis
assume squarefree N=pq and H<p<=q; a public schedule must pay for its guesses
and small-factor cases if claiming a full algorithm.

Uniform u over units projects uniformly to F_p^*. For each fixed i,j,
the equation i*u=j modulo p has exactly one unit solution. Therefore

    Pr[exists i,j: p divides i*u-j] <= H^2/(p-1).

The same holds at q. A proper split requires at least one of these events,
so a batch of K independently sampled unit coefficients has success at most

    min(1,K*H^2*(1/(p-1)+1/(q-1))).                  (1)

No independence between the H^2 pair events is assumed. Exact collisions
modulo N are removed by the stated consumer. An exact probability law would
also need the number of distinct short ratios j/i in each field; the upper
bound (1) is sufficient for the cost gate here. For K RAW samples initial
gcd exits are bounded by K*(1/p+1/q). For K ACCEPTED unit samples the
number of raw draws and all failures must instead be paid, with an explicit
cap or expected geometric-sampling bound. See the exact distinction in
[the primitive-ratio extension](W033-primitive-ratio-sharing.md).

## Two real implementations of sharing, both priced

**Explicit points.** Construct F(X)=product_(j=1..H)(X-j) once. Evaluate it
at the K*H supplied points i*u_k, using the exact-match exclusion when
needed. Ordinary generation explicitly visits K*H points; even with shared
F and fast multipoint evaluation its explicit data traffic is Omega(KH).
For constant success (1) requires K H^2=Omega(p). With H<=sqrt(p), the
traffic is then Omega(p/H)>=Omega(sqrt(p)); with H>=sqrt(p), even one H-point
trial is already at that scale. This is a lower bound for this explicit
representation and specified random generator, not for all factoring.

**Expand a polynomial in u.** Set

    Q_H(U)=product_(i=1..H) F(iU).

It has degree H^2 and unit leading coefficient (H!)^H on H<p. Expand it
in a literal dense array, then evaluate at K supplied u values. The array
has H^2+1 slots; the usual available construction/evaluation has soft
O(H^2+K) arithmetic cost, with logN-bit residues and paid polynomial
workspace. Obtaining proper factors from full products still needs the
original factorization tags or a reconstructed row; this only adds cost.
Its explicit work volume is at least H^2+K, and K H^2=Omega(p) makes that
Omega(sqrt(p)) by the arithmetic-geometric mean inequality.

Thus expansion removes repeated evaluation of the row circuit, but pays
for its degree. Both algorithms lose the hoped-for sub-square-root factor
search at this gate. This is not a theorem against an implicit aggregate
algorithm that does not build the degree-H^2 array; none is supplied here.

## Constructive implication

The exact failed assumption is that a two-dimensional grid creates H^2
useful chances while repeated coefficient choices can be consumed at only
H+K cost. We have explicit methods costing KH or H^2+K, and the elementary
success bound shows why either retains the square-root scale.

A successful changed computation would need either a generator with a
proved higher separating probability than these uniformly sampled slopes,
or a concrete aggregate evaluator avoiding BOTH point traffic KH and the
dense H^2 coefficient array. Merely stating either desired property is
not an algorithm. At present the independent canonical-floor branch is
the only active source of a different input-dependent distribution; its
unfiltered higher-digit yield remains unproved.
