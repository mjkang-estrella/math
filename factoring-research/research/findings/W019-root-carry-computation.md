# W019 parent continuation: what the root sharing actually removes

2026-10-08 local. Derived after delegating W019 A/B/C; this continuation was
not in their original frozen brief. No experiments, new complete bound, or
independent acceptance is claimed.

The A7 character-class parametrization replaces UV modular square-root
acquisitions by U+V acquisitions and constant-many roots C. Each entry still
requires a product, a remainder/carry and a collision query. Fast arithmetic
on the row/column lists is therefore a useful constant/bit-cost opportunity,
not a reduction of the UV record term in the proved cost envelope.

There is an additional ALL-INPUT restriction on a putative improvement.
Even if UV is of order m, U+V need not be sqrt(m). Near the smallest factor
size X~sqrt(N/m), the coverage rectangle has U of order m and V of order
one. An O~(U+V) algorithm would still cost m there. A balanced-semiprime
improvement would not by itself extend to the whole factor range. The
conditional N^(1/6) target in W019 requires saving work on these skewed
rectangles too, or a separately paid algorithm for those factor sizes.

## An explicit row-product representation, and its current cost

For one character chart, set c_v=alpha^(Nv), y_u=alpha^(2*C*A_u) and
x_u=alpha^u. Before the bounded representative/carry corrections, the row
product is the bivariate polynomial

    F(X,Y)=product_v (X*c_v-Y^(B_v)),  evaluated at (x_u,y_u).

This is a concrete arithmetic expression of V binomial factors. But a dense
expansion can have Y-degree sum B_v up to V*(m^2-1); exponents and output
traffic are not V just because its formula has V factors. Sequential sparse
evaluation at U points still costs UV modular powers. No fast resultant or
sparse multipoint bound has been supplied that makes this O~(U+V).

The required canonical root is s=r-m^2*c for r=2*C*A_u*B_v. The exact identity
alpha^s=alpha^r*beta^(-c) matters: beta has deliberately large order. A Fourier
or cyclic-polynomial trick that sets beta=1 changes the search problem.
Absorbing c into the searched t works for each explicit pair, but a common
uncentered t interval can be much wider than the true O(W/m^2) interval.
Thus it does not remove pair processing at the advertised small radius.

This gives a concrete next mathematical question: evaluate the indicated
binomial row products on the modular-root point sets AND their bounded
carry corrections without materializing the UV entries or large dense
degree, with full-modulus matches still recoverable. A scalar product
routine which cannot localize/handle global matches is not yet the consumer.

## A different attempted strengthening: higher-power congruence filters

Could the same short vector give a stronger congruence by powering (A2)?
Let F(S)=S^2-4uvN and k>=1. At this chart's roots m does not divide F'(S).
The condition F(S)^k=0 mod m^(2k) is equivalent to v_m(F(S))>=2, exactly
the original m^2 condition. Each simple root modulo m^2 lifts to
m^(2k-2) accepted residue classes modulo m^(2k); density has not improved.
Treating it as two roots modulo m^(2k) would discard valid covered sums.

Instead forcing u*p-v*q=0 mod m^a gives F(S)=0 mod m^(2a), but the generic
short-vector dictionary then has UV of order m^a. Renaming m^a as the
auxiliary modulus returns the same explicit-record balance. This does not
exclude better dictionaries or higher-degree computations; it identifies
the exact failed premise of this power-filter attempt.

A materially different escape must gain more than a squared modulus from
the SAME paid cover, or evaluate the structured dictionary implicitly. It
cannot get that gain by powering the existing congruence alone.
