# F004 — Cyclic quotients of affine five-space with exotic branch divisor

Status: **proved instance of a classical cancellation-to-action construction; independently accepted**. No first-example or dimension-optimality claim.

## Exact input

C denotes [An explicit failure of complex affine-space cancellation, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/build/sections/01-introduction.tex): an integral complex fourfold X≇A⁴ with X×A¹≅A⁵. Its [construction, `prop:stabilization`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/build/sections/02-construction.tex) supplies polynomial coordinates and inverses. These are accepted inputs. “Exotic” below means algebraically nonisomorphic to A⁴; no differential-topological claim is needed.

**Statement.** There is a smooth connected affine complex fourfold X, not isomorphic to affine four-space, such that for every integer (m\ge2) there is a faithful algebraic action of (\mu_m) on (\mathbb A^5_\mathbb C) with all of the following properties:

1. Every nonidentity group element has fixed subscheme isomorphic to X, a smooth hypersurface.
2. The affine quotient is again (\mathbb A^5); its quotient map is finite flat of degree m. Its reduced branch divisor is isomorphic to X.
3. The action is not conjugate by a polynomial automorphism to any linear action.
4. Its product with the trivial action on one affine line is polynomially conjugate to the diagonal action on (\mathbb A^6) with five trivial coordinates and one coordinate of weight one.

The actions are restrictions of a single faithful algebraic (\mathbb G_m)-action on (\mathbb A^5), also nonlinearizable and linearizable after one trivial-line stabilization. The torus quotient is X (unlike the finite cyclic quotients).

**Proof.** Take X from C and fix an isomorphism (\phi:X\times\mathbb A^1_w\to\mathbb A^5). The product being smooth implies X is smooth: tangent dimensions and local dimensions both increase by one on taking a product with a line. X is integral, hence connected. On the product let (\lambda(x,w)=(x,\lambda w)). Transport this action through \(\phi\). Faithfulness is immediate. For any scalar \(\lambda\ne1\), the fixed ideal is \((w)\), since \(\lambda-1\) is invertible. Thus the fixed subscheme is X. The group-fixed scheme is also X×{0}.

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
The second isomorphism acts only on fixed coordinates; the action on w remains scalar multiplication. Explicitly, the single polynomial isomorphism F(φ(x,w),z)=(φ(x,z),w) conjugates every stabilized action to (y,w)↦(y,λw). It is independent of λ and m. This proves the claimed linearization, simultaneously for the torus and all its finite subgroups. Torus invariants are exactly A. QED.

**Explicit input.** C uses
\[
 A=\mathbb C[p,s,u,F,J]/(H),\quad x=s^2+u^3+p^2F,\quad
 H=x^2F-(1+2sx)J-p^2J^2-pu.
\]
The cited Proposition supplies \(\phi\) and its inverse by finite formulas. Thus transporting the action is an effective polynomial construction, although expanded five-coordinate automorphism formulas are not provided here.

**Additional immediate corollary.** The map ((x,w)\mapsto(x,0)), transported by \(\phi\), is an idempotent polynomial endomorphism of (\mathbb A^5), of differential rank four everywhere, whose image is X. It cannot be polynomially conjugate to a linear idempotent. The retract algebra is not isomorphic to a polynomial algebra, although the idempotent map itself is polynomial; but should be grouped with the same construction, not counted as an independent discovery.

**Novelty check.** The full cancellation TeX, including its affine-fibration section, contains no cyclic-action, involution, retract, or affine-action linearization corollary. Its occurrences of “linearization” concern lifting actions to line bundles, a different statement. Crucially, [Kraft, *Affine n-space, C*-actions and related problems*, opening discussion](https://indico.ictp.it/event/a02281/contribution/19/material/0/0.pdf) explicitly records the cancellation-to-involution fixed-locus argument. The method is therefore classical. The new contribution here is the concrete dimension-five instance and the combined polynomial-quotient/branch/stabilization statement under C. No claim of a newly invented implication or first-ever nonlinearizable action is justified by this search. “Linearization” throughout means polynomial conjugacy, not birational or holomorphic conjugacy.

## Branch structure and scope

Writing B=A[v] and S=B[W]/(W^m−v), the relative differentials are
Ω_(S/B)=S/(w^(m−1)) dw. The discriminant is a nonzero complex constant
times v^(m−1). Thus the reduced branch divisor is X, the discriminant
divisor has multiplicity m−1, and its scheme-theoretic pullback is V(w^m).
These are distinct statements. The torus quotient is the affine categorical
quotient X, not a geometric orbit quotient.

The published prior mechanism appears in [Kraft, *Challenging problems on
affine n-space*, Bourbaki 802 (1996), §1 p.296](https://www.numdam.org/item/SB_1994-1995__37__295_0.pdf).
The reviewed contribution is the dimension-five cyclic instance and its
quotient/branch/stabilization properties under the accepted new cancellation
input. This proves no characteristic-p transfer, expanded coordinate-degree
bound, holomorphic nonconjugacy, or minimum-dimension statement.

## Validation

[Independent review](../reviews/cyclic_actions-r1.md) accepted the theorem
and optional retract after checking the source coordinate construction,
fixed schemes, finite freeness, ramification and simultaneous conjugacy.
Its six presentation suggestions are incorporated, using the explicitly
algebraic meaning of “exotic.” The parent independently checked invariants,
the fixed-locus obstruction and the displayed conjugacy. No finite sampling
is needed for these ring identities. No proof-assistant verification is
claimed.
