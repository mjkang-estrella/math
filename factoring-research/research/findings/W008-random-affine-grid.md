# W008 — affine random grids with a paid block evaluator

2026-10-08. Parent constructive alternative, PROVISIONAL. No experiment,
new solver/Lean code or established factoring improvement. W008 A continues
on arbitrary random lists; this note changes the generator to five random
residues and adds structure to the scalar product.

## Five random parameters, K^4 local tests

Choose b,a_1,a_2,a_3,a_4 independently uniformly modulo N=pq, p<q odd
distinct primes. For v in {0,...,K-1}^4 let

    L_v=b+sum_i a_i*v_i  mod N.

The array is described by five residues and K; no K-list expansion is
needed merely to specify it. For K<=p, different v,w are distinct modulo
both p and q. The linear forms in the five random parameters have
coefficient vectors (1,v) and (1,w), which cannot be scalar multiples
over either prime field. Thus the candidate pairwise-independent useful
indicator law of W008 holds verbatim:

    a=(1/p)(1-1/q),
    lambda=K^4*a,
    Pr[some p-only zero] >= lambda/(lambda+1-a).

Global-zero probability is at most K^4/N. The shared random offset is
essential to this simple proof. Without it, scalar-proportional index
vectors give dependent events and v=0 is always a global zero. No
primitive-vector enumeration is needed with b present.

At the first power-of-two K with K^4>=p, K<=p for p>=2, and K^4<16p.
For p,q>=131 the same provisional constant success (>1/3) after the
one-path full-gcd descent follows. Descents restrict coordinate intervals
and translate b; the compact representation is preserved.

The pairwise-independence assertion is NOT silently extended to K>p.
A schedule may be proved separately or use a paid dovetail across scales;
the old arbitrary-list monotonic probability argument needs rechecking.
There is no hidden factor input to this generator.

## Exact block product over the composite ring

Write R_K(b,a)=product_v L_v modulo N. First suppose K=m*h exactly.
Write every coordinate v_i=r_i+m*q_i, with 0<=r_i<m, 0<=q_i<h.
Build the single-variable monic polynomial

    F(T)=product_(r in [0,m)^4) (T+sum_i a_i*r_i).

Evaluate it at all h^4 points

    x_q=b+m*sum_i a_i*q_i.

Then R_K is exactly product_q F(x_q). This is a real algorithm: enumerate
m^4 inner shifts, build their monic product tree, enumerate h^4 outer
points, perform monic remainder-tree evaluation, and multiply the results.
No field interpolation or inverses of differences are required. Using
fast modular polynomial arithmetic its work is

    (m^4+h^4)*poly(log N+log K),

with the coefficient, point and output records counted. With m,h near
sqrt(K), it costs K^2*poly(log N+log K). For powers of two, choose m as
2^floor(log2(K)/2), leaving h/m at most 2.

Arbitrary rectangular subboxes used in recovery are handled by splitting
individual coordinate lengths into blocks plus remainders, at most 2^4
types per chosen split. Alternatively pad a requested interval by a
dyadic decomposition and multiply the O(log(K)^4) subbox products. The
subbox construction and all factors are charged; no extra leaves may be
silently included.

This supplies a composite-ring control without constructing the two
degree-K^2 composed-sum polynomials or using factorial denominators.
It does NOT reduce the critical exponent. Within this materialized
single-block scheme, m^4+h^4>=2K^2, so changing the split cannot help.
This is a restriction on these actual records, not on every algorithm.

## Why an obvious small-order shift recurrence fails generically

Let G_K(X)=product_(v in [0,K)^4)(X+sum_i a_i*v_i) over Q(a_1,...,a_4).
All K^4 roots are distinct. For a nonzero integer vector h, put gamma=a·h.
The number of common roots of G_K(X+gamma) and G_K(X) is

    I(h)=product_i max(0,K-|h_i|).

After cancelling their gcd, both numerator and denominator of
G_K(X+gamma)/G_K(X) have degree K^4-I(h). For a nonzero shift this is
at least K^3: a unit coordinate shift attains equality. A shift not
equal to a difference of grid roots has no cancellation at all.

Hence this family does not supply a scalar FIRST-ORDER shift equation
with bounded-degree polynomial numerator and denominator through
ordinary cancellation. The surviving face is large. Treating that
degree as a constant inside a matrix-factorial/holonomic algorithm is
invalid. This does not exclude higher-order recurrences, a compact
face evaluator, specialization-specific identities, nonlinear changes,
or calculations existing only modulo N.

The proof over independent symbolic slopes is not a statement that four
rational numbers are Q-linearly independent. For an integer specialization
it applies only when distinct relevant bounded coefficient vectors have
distinct dot products. Small-base or aligned slopes may fail that condition.
In particular a_i=a*K^(i-1) makes the full box an ordinary length-K^4
arithmetic progression: it has a different shift overlap, but its standard
factorial evaluator again has square-root-of-length K^2 cost.

## Complete costs and a different next computation

Source input traffic is now O(log N+log K) for fixed dimension, so an
arbitrary-list input-size objection or worst-case 4SUM reduction cannot
simply be imposed on this compact promise. The actual product algorithm
still writes K^2 records. To change the conclusion, produce a scalar-only
grid algorithm below K^2 with setup, modular bit widths and the O(log K)
recovery calls included. No such algorithm is supplied here.

Primary leads for the precise recurrence-computation scope:
- Bostan--Yurkevich, Fast Computation of the N-th Term of a q-Holonomic
  Sequence and Applications, https://arxiv.org/abs/2012.08656 .
- The accepted H029/H030 files already distinguish fast monic product
  computation from output-size obstructions. Do not duplicate their
  nonpolynomial Lehman floor-root representation audit; this grid has
  exact affine leaves and a different random generator.

A review should prove/correct the generator and boundary count, give
the paid rectangular product/recovery bound, and check whether an
existing constant-order recurrence theorem actually applies. Do not
call a multiple-gamma symbol or a general norm a fast modular evaluator.

