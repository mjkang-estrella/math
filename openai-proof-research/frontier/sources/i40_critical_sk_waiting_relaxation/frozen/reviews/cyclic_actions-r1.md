# Independent review: cyclic actions, round 1

Date: 2026-10-08. Scope: `proposals/algebra_geometry.md`, section 1, including its optional retract corollary. No prior review findings or responses. Upstream proofs are accepted as true, as instructed; this review checks their statements and the new deductions, not upstream correctness.

**Verdict: ACCEPT.** All four numbered conclusions, the common torus action, simultaneous linearization after one trivial stabilization, and the retract corollary follow from the stated upstream input. No mathematical correction is required. The presentation improvements below make scheme structures, effective transport, terminology, and novelty limits more explicit. This is acceptance as a substantive downstream corollary, not certification of literature priority.

## 1. Exact dependencies and source checks

Read `AGENTS.md`, `sources/upstream.json`, catalogue entry 047 in `sources/CONTENTS.md`, and the relevant paths in the complete `sources/preprints-tree.json`. The immutable revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The only nonstandard mathematical input needed for the main assertion is:

> There is a finitely generated integral complex algebra A of dimension four such that A[w] is a polynomial complex algebra in five variables, but A is not a polynomial complex algebra in four variables.

This is exactly Theorem `thm:main` in [the pinned introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/build/sections/01-introduction.tex). The displayed presentation in the proposal agrees with equation `eq:example` there.

Effectivity additionally uses Proposition `prop:stabilization` in [the pinned construction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/build/sections/02-construction.tex), specifically the finite exponential, polynomial representative `con:e-polynomial`, divisibility certificate `con:e-certificate`, and final coordinates `con:polynomial-cylinder`. I read those formulas and their inverse construction. Independent retrieval of the introduction, construction, affine-fibration section, and main TeX from pinned raw GitHub URLs matched the local cached bytes exactly.

Catalogue entry 047 lists one cancellation manuscript; the complete path listing supplies no separately titled cancellation companion. Its introduction and [affine-fibration section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/build/sections/07-affine-fibrations.tex) state stable-coordinate and fibration consequences, not this cyclic-action package. A targeted search of the complete cached manuscript found no cyclic, involution, or retract statement; its linearization occurrences concern line bundles. This supports the limited statement that the corollary is not already explicitly formulated in that manuscript, not an exhaustive repository-wide or literature-wide absence claim.

## 2. Complete verification of the deductions

Put X = Spec A and fix a complex-algebraic isomorphism φ: X × A¹ → A⁵ once and for all. All actions and isomorphisms below are over C. The same X and φ work for every integer m ≥ 2.

### Smoothness and connectedness

At every closed point x of X,

\[
T_{(x,0)}(X\times\mathbb A^1)=T_xX\oplus\mathbb C.
\]

The left side has dimension five and the local dimension of X at x is four. Thus X is regular at every closed point. Since X is of finite type over the perfect field C, it is smooth: a nonempty nonsmooth locus would contain a closed point. This justifies the proposal's tangent-space argument without incorrectly inferring smoothness merely from being a closed subvariety of a smooth variety. Integrality gives connectedness.

### A single faithful action and its fixed schemes

On X × A¹_w define s_λ(x,w) = (x,λw), and set α_λ = φ s_λ φ⁻¹. This is an algebraic G_m-action because the full parameterized map is regular. Its kernel is trivial, as already seen on the w coordinate. Restriction to μ_m is faithful, and a primitive m-th root gives an automorphism of exact order m.

For every complex scalar λ ≠ 1 the equalizer ideal is

\[
I_\lambda=(s_\lambda^*f-f:f\in A[w])=(w).
\]

All differences are divisible by w, and the difference for f = w is (λ−1)w. Thus the fixed scheme is reduced and equals X × {0}, not just set-theoretically. This works also for nonidentity elements of proper order dividing m. The entire μ_m-fixed scheme and the entire G_m-fixed scheme are the same scheme. The ideal (w) defines a smooth effective Cartier divisor; transport preserves that property.

### Invariants, quotient, rank, and branch

Let ζ be a primitive m-th root. For f = Σ a_i w^i, invariance is equivalent to (ζ^i−1)a_i = 0 for each i. Every nonzero complex scalar is a unit in A, so exactly the multiples of m survive. Hence

\[
A[w]^{\mu_m}=A[w^m]\cong A[v]\cong\mathbb C^{[5]}.
\]

The last isomorphism uses the same cylinder theorem with its independent variable renamed v; it does not assert that A itself is polynomial. The affine quotient is therefore A⁵. Write its coordinate-ring extension as

\[
B=A[v]\longrightarrow S=B[W]/(W^m-v)\cong A[w].
\]

Division by the monic polynomial shows that 1,W,…,W^(m−1) form a B-basis. Thus the quotient map is finite locally free, indeed free, of constant rank m, and faithfully flat. Its function-field degree is also m, since A is a domain. Choosing φ on the source and the renamed copy φ_v on the target gives the polynomial map φ_v ◦ ((x,w) ↦ (x,w^m)) ◦ φ⁻¹ between two copies of A⁵.

For exact ramification information,

\[
\Omega_{S/B}\cong S/(m w^{m-1})\,dw
             \cong S/(w^{m-1})\,dw.
\]

Consequently the non-étale locus has support V(w), and the map is étale everywhere else. Its image has support V(v), which is a smooth divisor isomorphic to X. Equivalently, the discriminant of W^m−v is a nonzero complex constant times v^(m−1). Thus the **reduced branch divisor** is exactly V(v). The adjective “reduced” in the proposal is correct and necessary: the discriminant divisor has multiplicity m−1, while the full inverse image of V(v) is V(w^m). The restriction V(w) → V(v) is the identity on X. The generic ramification index along this divisor is m.

### Nonlinearizability

For a linear representation of μ_m on C⁵ the group-fixed scheme is the vector subspace defined by all linear equations (g−1)y = 0. A conjugacy intertwines scheme-theoretic fixed loci. Since the constructed fixed scheme has dimension four, a linearization would give X ≅ A⁴, contradicting precisely the accepted nonpolynomiality input. The same argument applies to G_m. It also shows that every individual nonidentity element of the constructed cyclic group is nonlinearizable as an automorphism, if that strengthening is desired.

### One trivial stabilization, uniformly in m

Define an isomorphism F: A⁵ × A¹_z → A⁵ × A¹_w by

\[
F(\phi(x,w),z)=(\phi(x,z),w).
\]

Both directions are regular, so this is a polynomial automorphism after identifying source and target with A⁶. Direct substitution gives

\[
F\circ(\alpha_\lambda\times\mathrm{id})\circ F^{-1}(y,w)
    =(y,\lambda w).
\]

This **single F**, independent of λ and m, linearizes the entire torus action and all finite cyclic restrictions simultaneously. The added z coordinate has trivial action. The resulting representation has five trivial coordinates and one weight-one coordinate, exactly as claimed. There is no equivariance requirement on φ with respect to any upstream action.

For the torus, the same coefficient calculation gives A[w]^(G_m) = A, so its affine categorical quotient is X. This is not a geometric orbit quotient: over a closed point x there are the zero orbit and the nonzero w orbit. No assertion of a geometric torus quotient should be substituted for the present affine quotient statement.

## 3. Effectivity and optional retract

The source supplies more than an abstract stabilization. In its notation, Φ = exp(wΔ) and Φ⁻¹ = exp(−wΔ) are finite polynomial substitutions. The intermediate quotient T has polynomial coordinates p,s,u,M,e, with L = L_* + p³e and w = W(e). The expressions involving division by p³ have polynomial representatives certified in the source; they are not merely rational formulas on p ≠ 0. The determinant-one inverse change recovers F,J. Transport back by Φ⁻¹ gives the five cylinder coordinates.

Therefore φ and φ⁻¹ can be computed by finite polynomial arithmetic, and α_λ is obtained by substituting λw between these two maps. This proves availability of an effective polynomial construction, including at p = 0. It does not provide expanded coordinate lists or a useful bound on their polynomial degrees. The finite-cover degree m is established above; it must not be confused with the total degree of the transported coordinate polynomials. There is no gap requiring an explicit expansion to establish the existential theorem or the stated effectivity claim.

The retract r = φ ◦ ((x,w) ↦ (x,0)) ◦ φ⁻¹ satisfies r² = r. At (x,w), its differential sends (ξ,a) to (ξ,0), with tangent spaces on X at the same x; its rank is four everywhere. Its image, including its scheme-theoretic image, is φ(X × {0}). On rings the associated idempotent has image A under the chosen identification A[w] ≅ C^[5], giving an algebra retract which is not a polynomial algebra. A polynomial conjugacy to a linear idempotent would identify its image with a four-dimensional vector subspace, again contradicting the input. The optional corollary is correct and belongs to this same construction.

## 4. Literature and novelty assessment

The general mechanism is demonstrably classical. Independently of the scanned ICTP item cited in the proposal, Hanspeter Kraft's [*Challenging problems on affine n-space*, Séminaire Bourbaki 802, Astérisque 237 (1996), §1, p. 296](https://www.numdam.org/item/SB_1994-1995__37__295_0.pdf) explicitly uses (y,z) ↦ (y,−z) on a polynomial cylinder and its fixed locus to deduce that linearization would imply cancellation. This is an independently checked, precise replacement or additional reference. I could retrieve the ICTP scan, but it supplied no extractable text; I do not rely on independent verification of its wording or page location.

For historical significance, Vladimir Popov's [*Variations on the theme of Zariski's Cancellation Problem*, arXiv:1901.07030v2 (2019), discussion following Proposition 34](https://arxiv.org/html/1901.07030v2) describes existence of nonlinearizable finite abelian actions on affine spaces as unresolved at that time. That makes the cyclic specialization meaningful, but is not evidence of priority in October 2026. The search did not establish whether the full quotient/branch/stabilization package has appeared elsewhere. Those additions are short formal consequences of the same product construction, so packaging them does not by itself establish a new method or independently deep theorem.

Accordingly retain “new-to-this-project consequence of the accepted cancellation theorem”; do not strengthen this to first example, least possible dimension, new general mechanism, or proven new-to-literature package. In particular, known nonlinearizable actions for other groups neither duplicate nor establish priority for these cyclic actions.

## 5. Concrete presentation changes and failure boundaries

These are nonblocking improvements:

1. After the fixed-ideal computation, explicitly say that the group-fixed scheme is also V(w). This connects the elementwise assertion to the nonlinearizability proof.
2. Add the displayed formula for F above to make “simultaneously” completely unambiguous.
3. Add the relative-differential or discriminant calculation if distinguishing branch, ramification, and pullback scheme structures matters in the final statement. Keep “reduced branch divisor.”
4. Clarify that “nonpolynomial retract” means “a retract algebra not isomorphic to a polynomial algebra”; the idempotent map itself is polynomial.
5. Specify what “exotic” means. The theorem proves nonisomorphism to A⁴ directly. Also X(C) is contractible, since X(C) × C ≅ C⁵ and the product retracts onto X(C). If the stronger differential-topological usage is intended, Kraft's cited survey, §2, Proposition 1, p. 298, records that a smooth contractible affine complex variety of dimension greater than three is diffeomorphic to C^d. This applies to the present fourfold, but cite it rather than silently importing the topological conclusion. No biholomorphic classification is proved here.
6. Add Kraft's precise published reference and retain the existing cautious novelty language.

The proof uses characteristic zero (in particular m is invertible and all m-th roots of unity are available). It should not be transferred unchanged to the constant cyclic group in characteristic dividing m. A scalar action of weight other than one may fail faithfulness unless the weight is coprime to m. The conclusion requires a one-line polynomial cylinder, not merely stable polynomiality after an unspecified number of variables. The stabilizing line must carry the trivial action for the stated representation and formula. Nonlinearizability here is polynomial conjugacy only, and no birational or holomorphic obstruction follows from this proof. Smoothness is not being inferred from an arbitrary hypersurface presentation or an arbitrary retract.

**Disposition:** accept section 1 and the optional retract corollary, with the six editorial clarifications recommended. No upstream proof audit, proposal edit, staging, commit, or agent delegation was performed.
