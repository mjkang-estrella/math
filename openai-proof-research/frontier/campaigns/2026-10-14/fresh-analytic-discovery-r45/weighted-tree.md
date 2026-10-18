# Weighted common-time-tree calculation — technical support only

Author: Myeongjin Kang. Original text, CC BY 4.0. This is an author-side
deduction from stipulated family 080 operations, not an independently reviewed
result or a campaign nominee. Written after exploratory calculation; no earlier
scope freeze is claimed.

Let n≥2, s=n/[2(n+1)], and let p>2 be the fixed exponent of the higher-dimensional
source's Proposition e:short-time (n≥3), or the planar companion's Proposition
prop:shortmax (n=2). Fix

    2<r<min(p,2(n+1)/n), q=r/(r−1), α=2/q,
    δ=n+2s−2n/q=2s−n+2n/r>0.

Then, conditional only on that source proposition and its displayed kernel
integration-by-parts estimates, the source common-tree proof gives

    ||sup_{0≤t<1}|S(t)f|||_{L^r(Ω)} ≤ C(n,p,r)||f||_{H^s(R^n)}             (1)

for every translated unit ball Ω and initially every compact-frequency L²
input. Extension by completion uses the same maximal-norm approximation as
the source. The planar short-time, kernel-localization and time-tree proofs
were checked after the initial n≥3 calculation; they supply the identical
interfaces with s=1/3. No candidate was frozen or nominated.

## 1. Weighted descendant estimate

Fix one measurable graph τ:Ω→[0,1) and w∈L^q(Ω), initially bounded. Use the
source's G_N(J), d_j(J), N=2^j, but now put

    m_J=∫_{τ∈J}|w|^q dx.

For J⊂I∈D_j at relative depth k≤j let a=2^(−k). Its time width is a/N.
We claim

    d_j(J) ≤ C a^δ m_J^α.                                          (2)

Partition space into cubes Q of side a. On one cube rescale x=x_Q+aX,
t=t_J+a²T, ξ=η/a. Squared Fourier norm contributes a^n; normalized
frequency contributes another a^(2s). The rescaled input weight W(X)=w(x_Q+aX)
has L^q norm a^(−n/q)m_{J,Q}^{1/q}. Since r<p, q>p'; on a fixed finite-volume
cube L^q embeds into L^{p',1}, with constant depending only on p,q,n.
Dualizing e:short-time therefore gives single-cube energy at most

    C a^(n+2s−2n/q)m_{J,Q}^{2/q}.

This includes Na=1 by the source's bounded-frequency case. A fixed number
of neighboring cube offsets are controlled by Hilbert Cauchy–Schwarz and
bounded multiplicity. As α>1, their sum is at most C a^δ m_J^α.

For the other offsets the source spatial nonstationary-phase estimate is

    |K_N(x−y,τ(x)−τ(y))| ≤ C N^n(1+N|x−y|)^(−n−2).

Call this majorant k_N. Its L^{q'/2} norm is
C N^{n(2/q−1)}. Young's convolution inequality followed by Hölder bounds
the corresponding absolute pairing by

    C N^{n(2/q−1)} ||w 1_{τ∈J}||_q².

After N^(−2s) normalization this is C N^(−δ)m_J^α≤C a^δ m_J^α,
since Na≥1 and δ>0. This proves (2). The calculation uses the positive
kernel majorant only in the nonstationary region; it does not assert that
this estimate holds for every pair of points on the graph.

## 2. One common weighted tree

The source initial-time separation is unchanged except for its error:

    d_j([0,1)) ≤ C Σ_{I∈D_j}d_j(I)+C 2^(−2j)||w||_1².              (3)

This follows by integrating the uniform far-time kernel bound once over
all far pairs. There is no count of interval pairs. Neighboring time bins
have bounded multiplicity. Hölder gives ||w||_1≤C||w||_q.

Follow the child of larger m-mass for j generations starting from I∈D_j.
Let P(I,k) be the lighter child at relative step k, and H(I,j) the terminal
heavy interval. These pieces partition I, including atoms, with half-open
dyadic intervals. Additivity and weighted Cauchy–Schwarz applied to (2) give

    d_j(I) ≤ C Σ_{k=1}^j 2^(−δk/2)m_{P(I,k)}^α
                   + C 2^(−δj/2)m_I^α.                            (4)

For child masses b≤a,

    (a+b)^α−a^α−b^α ≥ (2^α−2)b^α.

The proof is differentiation of (u+1)^α−u^α−1 for u≥1, with the b=0 case
immediate. Telescoping over finite subtrees, then monotone passage, bounds
the sum of lighter-child α powers over any distinct parents by
m_root^α/(2^α−2). For each fixed k, the parents of P(I,k), as j≥k and
I∈D_j vary, are distinct: their absolute depth is j+k−1, and at fixed j
they lie below disjoint I. Hence summing (4), and then (3), yields

    Σ_{j≥1} d_j([0,1)) ≤ C m_root^α = C ||w||_q².                 (5)

This uses exactly the source's common-tree mechanism, with a different
additive mass. It is not a new time decomposition.

## 3. Duality and maximal completion

For a bounded-frequency input, Littlewood–Paley decomposition, Fourier
Cauchy–Schwarz, bounded annular overlap, and (5) bound
|∫w(x) S(τ(x))f(x) dx| by C||w||_q||f||_{H^s}. The low-frequency piece is
bounded by its Fourier L¹ norm. Taking L^r duality gives a uniform graph
bound. For a finite list of times, choose the first maximizer and its complex
phase; this produces the same graph for all frequencies. Increasing finite
lists exhaust rational times; continuity in time of compact-frequency
extensions gives (1). Truncation extends the dual estimate to every L^q
weight. Cauchy sequences in H^s are Cauchy in the local L^r maximal norm,
which gives the corresponding completed time-uniform representative in the
usual source manner. No global-in-space estimate is claimed.

## 4. Paid operations and limits

All decisive operations already occur in the source e:dual-square proof:
short-time weak duality, spatial rescaling, nonstationary kernels, one
heavy/light tree, and convexity-deficit telescoping. The changes are the
L^q mass and ordinary Young inequality. This is technical support, not
claimed substantial or new to literature.

The calculation requires both δ>0 and α>1, with constants diverging when
either tends to zero. It does not prove the endpoint r=2(n+1)/n; it also
requires r<p, where the source supplies no prescribed optimal p. Du–Zhang
2019, Introduction around (1.6)–(1.7), records higher-dimensional obstructions
to the larger conjectural output exponent, so one must not silently replace
the unspecified p by that exponent. Nor does (5) prove any finite Schatten
bound or orthonormal-density gain.
