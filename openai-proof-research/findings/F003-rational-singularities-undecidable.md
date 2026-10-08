# F003 — Undecidable rational singular-point existence on normal rational quartics

Status: **proved downstream corollary; independent review accepted**. Upstream truth is assumed; literature priority is unestablished.

## Exact input

H denotes [Hilbert’s tenth problem over the rational numbers, October 6, `thm:degree-normal-form`, item (ii)](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/build/sections/07-consequences.tex): rational solvability of a nonempty supplied sum of squares of integral quadratics has Turing degree 0′. Variables and coefficient heights are unrestricted.

**Statement.** No algorithm decides whether a geometrically integral normal affine hypersurface over Q of total degree exactly four has a Q-rational singular point, even on an effectively supplied family where every input comes with:

- a dense smooth open subset explicitly isomorphic to (\mathbb A^N\times\mathbb G_m);
- an explicit rational parametrization of that open subset and a rational smooth point.

Dimension and coefficient heights are unbounded. On the encoded family below, rational singular-point existence has Turing degree (0'). There is no total computable bound, from the input equations, on the height of some rational singular point whenever one exists.

**Construction and complete reduction.** The input in H is a nonempty list (q_1,\ldots,q_s\in\mathbb Z[x_1,\ldots,x_n]), each of degree at most two. Introduce independent t,u,v and put
\[
 S(x,t)=\sum_{i=1}^s q_i(x)^2+t^4,\qquad
 Y_q:\ uv-S(x,t)=0\subset\mathbb A^{n+3}.
\]
S is nonzero and has degree exactly four because the coefficient of (t^4) is one. Thus the displayed equation has degree exactly four, including when some or all original quadratics vanish identically. Put (N=n+1).

Over any extension field of Q, in the UFD (K[x,t,u]) the polynomial (uv-S) is primitive as a polynomial in v: u and the nonzero polynomial S are coprime. It has degree one and is irreducible over the fraction field, hence is irreducible in the polynomial ring by Gauss's lemma. This proves geometric integrality. Inverting u gives exactly
\[
 K[Y_q][u^{-1}]=K[x,t,u,u^{-1}],\qquad v=S(x,t)/u.
\]
This identifies a dense rational open chart. It is smooth since the partial derivative with respect to v is u. The point (x=0,t=0,u=1,v=S(0,0)) is an explicitly known rational smooth point, and rational points of this chart are Zariski dense.

The full gradient is
\[
 \partial_uF=v,\quad\partial_vF=u,\quad
 \partial_{x_j}F=-2\sum_iq_i\partial_{x_j}q_i,\quad
 \partial_tF=-4t^3.
\]
A rational singular point therefore has (u=v=0), and the equation implies
\(\sum_iq_i(x)^2+t^4=0\). Ordered-field positivity gives (q_i(x)=0) for every i and t=0. Conversely these equalities make F and every partial derivative vanish. Consequently there is an exact bijection
\[
 \{x\in\mathbb Q^n:q_1(x)=\cdots=q_s(x)=0\}
 \longleftrightarrow \operatorname{Sing}(Y_q)(\mathbb Q),
 \qquad x\longmapsto(x,0,0,0).
\]
The Jacobian criterion applies in characteristic zero to this integral hypersurface.

For normality, the geometric singular locus is contained in (u=v=S=0). Since S is nonzero in N independent variables, this set has dimension at most (N-1), whereas (Y_q) has dimension (N+1). Hence singularities have codimension at least two. A hypersurface in a regular scheme is Cohen–Macaulay and satisfies (S_2); regularity in codimension one gives (R_1). Serre's criterion proves normality, even after algebraic closure. See the [Cohen–Macaulay quotient lemma, 10.104.2](https://stacks.math.columbia.edu/tag/02JN) and [Serre's criterion](https://stacks.math.columbia.edu/tag/031S).

The construction is computable and maps H's undecidable list problem into the stated promised class. Enumeration of rational tuples, with exact evaluation of F and its gradient, semidecides singular-point existence, giving the upper Turing bound (0'). H gives the matching lower bound. This proves the decision and degree assertions. Finally, define affine height as the maximum of absolute numerator and positive denominator of each coordinate in reduced form. A computable bound for one singular point would allow a finite exhaustive search, deciding the problem, a contradiction. QED.

**Important limits.** This concerns rational points of the singular locus, not the technical property called “rational singularities.” Detecting whether the geometric singular locus is empty remains an algebraic computation. No fixed-dimension undecidability, isolated-singularity promise, or many-one completeness for the halting problem is proved. H explicitly establishes Turing degree (0'), not many-one completeness of H10(Q). The sum-of-squares implication is used only over Q, not over its algebraic closure.

**Novelty check.** H's full consequences section already states quartic and quadratic-sum-of-squares rational solvability; those are not our new result. It does not state the normal rational hypersurface/singularity packaging. Targeted searches for “rational singular points,” “quartic hypersurfaces,” and undecidability found no matching primary statement. [Garcia-Fritz–Pasten–Vidaux, *Effectivity for existence of rational points is undecidable*](https://arxiv.org/abs/2311.01958) studies rational-point problems with height-comparison conditions, rather than this singular-point promise. The construction is elementary and may already occur as a conditional reduction in other literature; absence from this bounded search is not a priority proof.

## Adversarial boundary checks

- The list q₁=0 gives uv=t⁴: the singular set has codimension exactly two,
  yet the hypersurface is normal. The t⁴ term prevents loss of integrality.
- The list q₁=1 gives a smooth hypersurface, hence a negative instance.
- For q₁=x²−1 and q₂=2x, the complex singular points x=±i, t=u=v=0
  exist even though the q_i have no common complex zero. Thus the bijection
  is only on rational points, where positivity is available.
- Naive projective closure invalidates the reduction: the homogenized
  equation uvw²−ΣQ_i(x,w)²−t⁴=0 always has a rational singular point
  [x=0,t=0,u=1,v=0,w=0] at infinity. This is an affine theorem.

The uv−S construction is the classical algebraic suspension; see
[Arzhantsev–Kuyumzhiyan–Zaidenberg, Definition 0.3 and Lemma 3.1](https://arxiv.org/html/1003.3164).
The additional conclusion here is its arithmetic undecidability under the
normality, rationality and supplied-chart promises, not a new construction
of rational varieties.

## Validation

[Independent review](../reviews/singular_quartics-r1.md) accepted the proof
and checked the upstream October and September consequence sections. Its
precise Stacks citation and counterexamples are incorporated here. The
parent checked Gauss's lemma, the codimension-two argument, rational-point
positivity, and the finite-search height-bound contradiction.

`python openai-proof-research/experiments/algebra_geometry.py` passed
101,250 exact rational Jacobian checks and chart identities. The separate
matrix-unit test in that exploratory script is unrelated to this theorem.
These finite checks support the reduction's algebra, not undecidability.
No proof-assistant verification is claimed.
