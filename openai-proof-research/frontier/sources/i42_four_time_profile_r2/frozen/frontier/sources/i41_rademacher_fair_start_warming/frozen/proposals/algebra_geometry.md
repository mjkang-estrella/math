> Archived exploratory draft. Some claims were corrected, rejected, or left unreviewed. Use [the final index](../README.md) and [screening decisions](../SCREENING.md) for accepted results.

# Algebra, geometry, and decidability: three downstream corollaries

Research date: 2026-10-08. All upstream theorems are accepted as true, as instructed. Revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. These are new-to-this-project deductions; none is certified new-to-literature. The first two are recommended for development.

| Rank | Proposed result | Assessment |
|---|---|---|
| 1 | Nonlinearizable cyclic actions on complex affine five-space, with polynomial quotient, exotic fixed hypersurface, and linearization after one trivial stabilization | Complete short proof; strong concrete consequence. The cancellation-to-involution mechanism is classical, so claim a new instance/package, not a new method. |
| 2 | Undecidability of rational singular-point existence for normal, geometrically integral, rational quartic hypersurfaces, with a supplied dense smooth rational chart | Complete reduction; not found in upstream consequences or the limited primary-literature search. Best candidate for a separately formulated theorem. |
| 3 | A torsion-free finitely presented group algebra containing infinite finitary matrix units and a nonzero finitely generated projective module of zero K-theory class | Complete proof; classical ring-theoretic mechanism, newly instantiated in this group-algebra class. Lower novelty priority. |

## Sources and scope of inspection

Read `AGENTS.md`, `sources/upstream.json`, the relevant catalogue entries in `CONTENTS.md`, and corresponding entries in `overview.tex`. Scanned the catalogue broadly, including Hodge/CM results, reconstruction, cancellation, abundance, direct finiteness, Deligne–Drinfeld, and finitely presented torsion groups. Actual TeX was retrieved for cancellation, both H10 versions, the Deligne–Drinfeld family, the torsion-group family, and characteristic-two/odd-characteristic direct-finiteness families. Every retrieved TeX is under `sources/cache/algebra_geometry/`, preserving its preprint-relative path.

**Retrieval caveat:** the supplied `tree.json` has `truncated: true` and 58,727 entries, ending before the preprints. I therefore queried the same revision's root tree, then its `preprints` subtree recursively (13,223 entries, `truncated: false`). No shared cache/index was edited. Actual manuscript downloads used the pinned raw URLs below.

- **C:** [An explicit failure of complex affine-space cancellation, introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/build/sections/01-introduction.tex), Theorem `thm:main`: an integral complex fourfold (X\not\simeq\mathbb A^4) with (X\times\mathbb A^1\simeq\mathbb A^5). [Construction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/build/sections/02-construction.tex), Proposition `prop:stabilization`, gives polynomial coordinates and inverse through a finite exponential and polynomial substitutions.
- **H:** [Hilbert's tenth problem over the rational numbers, consequences](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/build/sections/07-consequences.tex), Corollary `thm:degree-normal-form`: solvability of a supplied sum of squares of integer quadratic polynomials over Q has Turing degree (0'). Its proof gives the arithmetic-circuit reduction. The [introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/build/sections/01-introduction.tex), Theorem `thm:main`, asserts H10(Q) undecidability.
- **D:** [A torsion-free group algebra that is not directly finite, introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Torsion-Free-Group-Algebra-That-Is-Not-Directly-Finite-October-4-2026/build/sections/introduction.tex), Theorem `thm:main`: a finitely presented torsion-free group G with a finite two-dimensional classifying complex and (a,b,c\in\mathbb F_2[G]) satisfying (ab=1,ac=0,c\ne0), hence (ba\ne1).
- **T:** [An infinite finitely presented residually finite 2-group, introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-infinite-finitely-presented-residually-finite-2-group-October-5-2026/build/sections/introduction.tex), Theorem `thm:main`. Used for screening lower-priority alternatives, not for the recommended theorems.

## 1. Cyclic quotients of affine five-space with exotic branch divisor

**Statement.** There is a smooth connected affine complex fourfold X, not isomorphic to affine four-space, such that for every integer (m\ge2) there is a faithful algebraic action of (\mu_m) on (\mathbb A^5_\mathbb C) with all of the following properties:

1. Every nonidentity group element has fixed subscheme isomorphic to X, a smooth hypersurface.
2. The affine quotient is again (\mathbb A^5); its quotient map is finite flat of degree m. Its reduced branch divisor is isomorphic to X.
3. The action is not conjugate by a polynomial automorphism to any linear action.
4. Its product with the trivial action on one affine line is polynomially conjugate to the diagonal action on (\mathbb A^6) with five trivial coordinates and one coordinate of weight one.

The actions are restrictions of a single faithful algebraic (\mathbb G_m)-action on (\mathbb A^5), also nonlinearizable and linearizable after one trivial-line stabilization. The torus quotient is X (unlike the finite cyclic quotients).

**Proof.** Take X from C and fix an isomorphism (\phi:X\times\mathbb A^1_w\to\mathbb A^5). The product being smooth implies X is smooth: tangent dimensions and local dimensions both increase by one on taking a product with a line. X is integral, hence connected. On the product let (\lambda(x,w)=(x,\lambda w)). Transport this action through \(\phi\). Faithfulness is immediate. For any scalar \(\lambda\ne1\), the fixed ideal is \((w)\), since \(\lambda-1\) is invertible. Thus the fixed subscheme is X.

Writing (A=\mathcal O(X)), coefficient comparison in a polynomial in w gives
\[
 A[w]^{\mu_m}=A[w^m]\simeq A[v]\simeq\mathbb C^{[5]}.
\]
The inclusion (A[v]\hookrightarrow A[w]), (v\mapsto w^m), is free with basis (1,w,\ldots,w^{m-1}). This proves finite flatness and degree m. Away from (w=0), the derivative (mw^{m-1}) is invertible, so the map is étale. At (w=0) the fiber in the normal direction is (\mathbb C[w]/(w^m)), so the reduced branch divisor is precisely (v=0\simeq X).

A linear representation has a vector subspace as its group-fixed subscheme. A polynomial conjugacy would therefore identify X with affine four-space, contradicting C. For stabilization, add a coordinate z with trivial action and reorder:
\[
 (X\times\mathbb A^1_w)\times\mathbb A^1_z
   \simeq (X\times\mathbb A^1_z)\times\mathbb A^1_w
   \simeq\mathbb A^5\times\mathbb A^1_w.
\]
The second isomorphism acts only on fixed coordinates; the action on w remains scalar multiplication. This proves the claimed linearization, simultaneously for the torus and all its finite subgroups. Torus invariants are exactly A. QED.

**Explicit input.** C uses
\[
 A=\mathbb C[p,s,u,F,J]/(H),\quad x=s^2+u^3+p^2F,\quad
 H=x^2F-(1+2sx)J-p^2J^2-pu.
\]
The cited Proposition supplies \(\phi\) and its inverse by finite formulas. Thus transporting the action is an effective polynomial construction, although expanded five-coordinate automorphism formulas are not provided here.

**Additional immediate corollary.** The map ((x,w)\mapsto(x,0)), transported by \(\phi\), is an idempotent polynomial endomorphism of (\mathbb A^5), of differential rank four everywhere, whose image is X. It cannot be polynomially conjugate to a linear idempotent. This is a concrete nonpolynomial retract of a polynomial ring, but should be grouped with the same construction, not counted as an independent discovery.

**Novelty check.** The full cancellation TeX, including its affine-fibration section, contains no cyclic-action, involution, retract, or affine-action linearization corollary. Its occurrences of “linearization” concern lifting actions to line bundles, a different statement. Crucially, [Kraft, *Affine n-space, C*-actions and related problems*, opening discussion](https://indico.ictp.it/event/a02281/contribution/19/material/0/0.pdf) explicitly records the cancellation-to-involution fixed-locus argument. The method is therefore classical. The new contribution here is the concrete dimension-five instance and the combined polynomial-quotient/branch/stabilization statement under C. No claim of a newly invented implication or first-ever nonlinearizable action is justified by this search. “Linearization” throughout means polynomial conjugacy, not birational or holomorphic conjugacy.

## 2. Undecidable rational singular-point existence on normal rational quartics

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

For normality, the geometric singular locus is contained in (u=v=S=0). Since S is nonzero in N independent variables, this set has dimension at most (N-1), whereas (Y_q) has dimension (N+1). Hence singularities have codimension at least two. A hypersurface in a regular scheme is Cohen–Macaulay and satisfies (S_2); regularity in codimension one gives (R_1). Serre's criterion proves normality, even after algebraic closure. See the [Cohen–Macaulay quotient lemma](https://stacks.math.columbia.edu/tag/00N7) and [Serre's criterion](https://stacks.math.columbia.edu/tag/031S).

The construction is computable and maps H's undecidable list problem into the stated promised class. Enumeration of rational tuples, with exact evaluation of F and its gradient, semidecides singular-point existence, giving the upper Turing bound (0'). H gives the matching lower bound. This proves the decision and degree assertions. Finally, define affine height as the maximum of absolute numerator and positive denominator of each coordinate in reduced form. A computable bound for one singular point would allow a finite exhaustive search, deciding the problem, a contradiction. QED.

**Important limits.** This concerns rational points of the singular locus, not the technical property called “rational singularities.” Detecting whether the geometric singular locus is empty remains an algebraic computation. No fixed-dimension undecidability, isolated-singularity promise, or many-one completeness for the halting problem is proved. H explicitly establishes Turing degree (0'), not many-one completeness of H10(Q). The sum-of-squares implication is used only over Q, not over its algebraic closure.

**Novelty check.** H's full consequences section already states quartic and quadratic-sum-of-squares rational solvability; those are not our new result. It does not state the normal rational hypersurface/singularity packaging. Targeted searches for “rational singular points,” “quartic hypersurfaces,” and undecidability found no matching primary statement. [Garcia-Fritz–Pasten–Vidaux, *Effectivity for existence of rational points is undecidable*](https://arxiv.org/abs/2311.01958) studies rational-point problems with height-comparison conditions, rather than this singular-point promise. The construction is elementary and may already occur as a conditional reduction in other literature; absence from this bounded search is not a priority proof.

## 3. Invisible projective modules and infinite matrix units in a torsion-free group algebra

**Statement.** For the group G in D, (R=\mathbb F_2[G]) contains a nonunital copy of the algebra of countably infinite matrices with finitely many nonzero entries. It also has a nonzero cyclic projective right module P satisfying
\[
 R\simeq R\oplus P,\qquad [P]=0\text{ in }K_0(R).
\]
There is a nonzero idempotent e killed by every unital homomorphism (R\to M_d(K)), for every integer (d\ge1) and every field K of characteristic two.

**Proof.** Set (e=1-ba\ne0). From (ab=1), obtain (e^2=e), (ae=0), and (eb=0). For nonnegative i,j define (E_{ij}=b^iea^j). Cancelling adjacent ab pairs and using the two annihilation identities gives
\[
 E_{ij}E_{kl}=\delta_{jk}E_{il}.
\]
Moreover (a^iE_{ij}b^j=e\ne0). To prove linear independence, multiply any finite relation on the left by (ea^r) and the right by (b^se); only its ((r,s)) coefficient times e survives. Thus these are actual matrix units, giving the claimed embedding.

The complementary idempotents ba and e give (R=baR\oplus eR). Since (baR=bR), left multiplication by b is an isomorphism (R\to baR), with inverse left multiplication by a. Taking (P=eR\ne0) gives the decomposition and its K-theory consequence. Finally finite square matrices with a one-sided inverse have a two-sided inverse, so every stated representation kills (1-ba). QED.

**Novelty status.** This is a standard consequence of a one-sided inverse, newly applied to D's torsion-free group with finite two-dimensional classifying space. [Iovanov–Sistko, *On the Toeplitz–Jacobson algebra and direct finiteness*](https://arxiv.org/abs/1603.00109) studies precisely the universal one-sided-inverse algebra. The matrix-unit mechanism is classical, not novel. The torsion-free companion has no corresponding K-theory/projective-module corollary. Other direct-finiteness companions use finite matrix units for compression; that is not the infinite finitary subalgebra above. This deserves a corollary note, not a claimed new general ring theorem.

## Rejected and deferred alternatives

- **Quartic H10(Q), quadratic systems, and sum-of-squares undecidability:** explicitly already in H, Corollary `thm:degree-normal-form`.
- **Stable-coordinate counterexamples and nontrivial affine-three-space fibrations:** explicitly already in C, Corollary `cor:stable-coordinate` and Section 7.
- **A finitely presented periodic Kazhdan group/nonamenability:** already in the periodic-group companion, Corollary `cor:kazhdan`. T's all-2-group finite quotients and unbounded exponent are also stated in its introduction.
- **Fixed-rank complex representations of T's group:** Schur finiteness plus Jordan's theorem suggests useful finite-quotient and character-variety consequences, but the mechanism already applies to older finitely generated torsion groups. Not developed as a novelty candidate.
- **Free Grothendieck–Teichmüller Lie algebra dimension formulas:** the free-Lie/Witt-formula route is routine and less substantive than the two developed geometry statements; no new asymptotic claim is made.
- **Higher-dimensional cancellation examples by adjoining variables to X:** invalid as a construction here; (X\times\mathbb A^1) is already affine five-space. The one-line stabilization in Result 1 is precisely why its nonlinearizability disappears.

## Validation and remaining gaps

`python openai-proof-research/experiments/algebra_geometry.py` passes with no external dependencies: 101,250 exact rational tests of the singular-point equivalence on (uv=(x^2-a)^2+t^4), for a=1,2; exact rational-chart checks; and 1,296 matrix-unit multiplication checks in the universal algebra (ab=1\ne ba). The a=2 finite search is only a sanity check; it is not the proof of absence of rational square roots of 2. The general arguments above supply the proofs.

No mathematical deduction gap remains in the stated results, conditional on the accepted upstream theorems and the standard commutative-algebra facts explicitly cited. Remaining research work is bibliographic priority checking, choosing which statements warrant standalone exposition, and optionally expanding the explicit five-coordinate cyclic automorphisms using C's supplied coordinate isomorphism. No expanded formula or optimal dimension claim is asserted. No upstream truth audit, shared-file modification, staging, commit, or subagent creation was performed.
