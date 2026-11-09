# W021 parent continuation: degree and batch-shift costs

Derived while the independent W021 audits run; not included in their frozen
original brief. These are parent arguments pending validation, not accepted
complexity improvements or implemented fast arithmetic.

Boundary convention for all digit relabelling below: use b>=2; bounded small
lengths use the direct product. The evaluation theorem's fixed-variable
asymptotics also require its own finite-small-size fallback.

## Fixed higher degree gives an explicit cost hierarchy

Let f(T) be an integer polynomial of fixed degree d>=1. Write

    f(b*k+j) = a_d*j^d + sum_(0<=h<d) c_h(k)*j^h.

Build the block polynomial

    F(Y0,...,Y_(d-1)) =
      product_(0<=j<b) (1-alpha^(a_d*j^d)*product_h Y_h^(j^h)),

where j^0=1 including j=0. Evaluate Y_h=alpha^c_h(k). The identity is exact.
The degree in Y_h is sum_j j^h=O_d(b^(h+1)). The rectangular coefficient
box therefore has O_d(b^s) entries, s=d(d+1)/2. Degree-aware product trees
have the same soft construction envelope: at group size t, the box is
O_d(t^d*b^(d(d-1)/2)); multiplying by b/t nodes increases geometrically
to the full box when d>1. The d=1 case has a logarithmic level overhead.

Relabel powers of each Y_h into h+1 base-b digits AFTER constructing F.
There are s variables, each of degree O_d(b); the coefficient box remains
O_d(b^s). For FIXED d the same ring evaluation theorem proposed in W021 A
would give a total envelope (b^s+L/b)^(1+epsilon) times paid binary factors.
Balancing gives exponent s/(s+1): 1/2 for degree1, 3/4 for degree2, 6/7 for
degree3. Degree1 agrees with the existing geometric-product comparator.

This identifies an actual penalty of this representation: higher exponent
degree makes the coefficient box larger, despite short binary coefficients.
Do not apply the fixed-variable theorem uniformly to growing d, or replace
it by a unit-cost ring-operation claim. It is not a lower bound on different
representations. The useful next search is low-degree exponents with enough
coverage, not arbitrarily high-degree formulas justified by small circuits.

## A possible chart change, and an explicit obstruction

Replacing a prime auxiliary modulus by a prime power could permit truncated
p-adic square-root series on residue balls. Unlike a square-root lookup table,
each chart then has polynomial integer exponents to which the block technique
might apply. But its polynomial lift still differs from the bounded root by
a pair-dependent carry. Larger residue balls require a higher series degree;
smaller balls require more charts. Both costs must enter the product bound.

There is also a concrete coverage defect for the simplest 2-power version.
For M=2^k with k>=3 and hidden ratio p/q=1+M/2 modulo M, a congruence
u*p=v*q mod M with u odd forces v=u+M/2 mod M. If |u|,|v|<M/4 this is
impossible, although the even vector (u,v)=(2,2) is a short solution. Thus
the ordinary short-vector cover cannot simply be replaced by a cover of odd
weights having simple p-adic roots at comparable balanced side lengths.
An N-only algorithm must handle such allowed residue ratios; this is an
algebraic obstruction to that chart restriction, not a factoring lower bound.

A viable continuation must pay the nonsimple valuation strata, use a different
cover, or prove a paid auxiliary-modulus selection avoiding the bad strata.
Taylor expansion alone resolves none of these. This explains why changing the
root representation can introduce a new coverage cost even before evaluation.

## Several additive shifts of the same quadratic

Suppose K products have the same A,D,L and exponents A*i^2+D*i+C_t, with
the K offsets supplied in binary. The F(X,Y) from W021 A does not depend on
C_t. Reuse its coefficients and evaluate at all K*floor(L/b) full-block
points. For the incomplete block of length r=L mod b, construct F_r once
and evaluate at K tail points; this avoids paying K*b for explicit tails.
Point construction, products, outputs and all offset widths are still paid.

The candidate envelope becomes

    (b^3 + K*(1+L/b))^(1+epsilon) * paid binary factors.

Taking b near (K*L)^(1/4), capped at L, gives the corresponding tradeoff.
There is also an essential equal-input comparator: directly construct the
univariate polynomial product_i<L(1-alpha^(Ai^2+Di)*Y), then evaluate it at
the K values alpha^C_t, at O~(L+K) modular work plus binary powering. Therefore
the new block candidate is useful only when its full cost beats that bound.
For K up to roughly L^(1/3), (KL)^(3/4) can be smaller than L; for larger K,
the ordinary full polynomial is already preferable at the power-exponent
level. No batched saving may be claimed against K separate naive scans.

Changing alpha across retries changes the coefficient polynomial; the same
preprocessing is not reusable across fresh bases for free. Also, W019's
modular root/carry entries do not become quadratic exponents merely because
their defining congruence is quadratic. These are material scope boundaries.
