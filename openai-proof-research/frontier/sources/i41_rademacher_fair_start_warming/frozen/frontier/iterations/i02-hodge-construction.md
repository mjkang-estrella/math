# i02 — explicit cover and support attempts for the Mumford partner

Date: 2026-10-08. **Outcome: the requested substantial new Hodge case was not obtained.** This round constructs an explicit geometric carrier for a level-one cubic block, then tests actual ways of obtaining a supporting divisor/cylinder. None constructs a nonzero class in the required component of `CH²(A×B)`. The positive carrier calculation below is not being submitted as a new Hodge theorem or as a solution meeting the user's significance threshold.

I read `AGENTS.md`, the immutable pin and relevant catalogue entries, the Mumford R2, K3 R2 and partner R3 reviews, and the prior outcome. I searched the entire 37-file H8 cache and read the relevant Mumford/carrier/rigidity passages. All 37 hashes were reverified. No upstream theorem was re-audited, no withdrawal was used as a theorem, and no other agent was spawned. Retained writes are this report and `frontier/{sources,experiments}/i02_hodge/`. One verification output was briefly written to `/tmp/i02_hodge_check_verify.out` and then removed; that temporary write was outside the requested scope. No staging, commits, or shared-index changes.

## 1. Fixed target, contracts, and early prior art

All cohomology and cycles have rational coefficients unless scalar extension is explicit; `Q(1)` has weight −2. Fix an **actual** Mumford fourfold A with `End⁰(A)=Q` and the actual tensor-product Hodge group of the R3 review. Write `V=H¹(A)`. Use its repaired polarized split sixfold B and the sub-Hodge structure

\[
U\subset H^3(B),\qquad U(1)\simeq V\otimes_{\mathbf Q}K\simeq V^{\oplus2}.
\]

The target is an algebraic class with nonzero projection to `[H¹(A)⊗U](2)`. The equivalence with `U⊂N¹H³(B)` is used with the exact Gysin/support convention of R3 §5.3. An algebraic projector onto U is not this target.

The accepted sources are at OpenAI/math **fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb**. Exact URLs and SHA-256 hashes, including reused cached PDFs, are in [the manifest](../sources/i02_hodge/manifest.json).

* **CM, Theorem 1.1; Lemma 8.1; Corollary 8.2.** The last requires a CM abelian target X and `W⊂Hᵏ(X)` with W(r) effective. It produces a closed support of codimension at least r. Lemma 8.1 realizes a simple **CM** effective twist in cohomology of an auxiliary CM abelian variety. The proof algebraizes the map using HC on the product of the two CM varieties. Neither hypothesis can be replaced by “has an algebraic projector.”
* **Covers, Theorem 1.1.** HC on all powers of `Jac(C_s)×M`, for s tensor Hodge-generic in the **full marked variation** of the fixed abelian cover, and every CM M. It is not GHC and does not apply automatically to a constrained exceptional subfamily. **§2 and Lemma 3.4** supply top character determinants from full cohomology of CM abelian varieties; they do not supply arbitrary tensor products of three distinct rank-two characters.
* **Weil, Theorem 1.1.** HC on all powers of a sixfold with the specified hyperbolic homological Hermitian polarization. Signature alone is insufficient; no coniveau statement for U is included.
* **K3, Theorems 1.1–1.2.** One exact full even-Clifford tensor implies HC/GHC on the K3 powers; its rank-eight quadratic embedding theorem does not construct the rank-nine Mumford tensor.

Early primary-literature checks were decisive:

1. [BHPS, arXiv:2510.00093v2](https://arxiv.org/pdf/2510.00093v2), §§5.1–5.3, already gives the hypergeometric covers
   `X₇,t: y⁸⁴=x¹³(x−1)⁴³(x−t)²⁹` and
   `X₉,t: y³⁶=x⁵(x−1)¹⁹(x−t)¹³`.
   Conjectures 5.1–5.2 ask for their tensor links to the genus-four families, including two CM elliptic factors and a Tate twist. The existence of the corresponding algebraic correspondence is explicitly left open. I do not promote these conjectures to source contracts.
2. [Moonen–Oort, *The Torelli locus and special subvarieties*](https://webspace.science.uu.nl/~oort0109/ModuliHandbook-moonenoort.pdf), Example 5.6 and Proposition 5.9, already treats `y⁹=x(x−1)(x−t)`, its genus-seven Jacobian, its CM elliptic old part, and its six-dimensional new part tracing a PEL curve. Thus the curve/Prym realization in §3 is classical, not a discovery.
3. H8 **a80abf628c5f05236372e97dbfaa5b316463e9df**, `11c_mumford.tex`, `thm:mumfordks`, `cor:mumfordksproducts`, `rem:mumfordunitary`, and `rem:mumfordpowersopen`, already contains the all-powers/KS links, unitary sixfold carrier, and explicit cautions about the missing algebraic link. `11d_mumfordrigid.tex` retains the seven-dimensional KS Hodge locus. Those reductions are not new results here.
4. [Arapura, arXiv:1201.6403v1](https://arxiv.org/pdf/1201.6403v1), Theorems 3.2 and 3.4, supplies a genuine GHC theorem for certain cyclic covers, but with specific base/branch and numerical hypotheses. The prime-degree projective-space/hyperplane theorem does not cover the weighted composite-degree quotient below. The more general theorem requires its motivic-dimension and Hodge-number inequality; neither is waived.
5. [Ein–Lazarsfeld, arXiv:alg-geom/9603017v1](https://arxiv.org/pdf/alg-geom/9603017v1), Theorem 1, says an irreducible theta divisor is normal with rational singularities. This is a restriction on the proposed theta support, not a source of the missing cycle.

This is a bounded prior-art audit. It establishes exact overlaps and scope restrictions, not novelty by absence of search hits.

## 2. Attempt A: make the CM coniveau construction supply U

The attempted construction was to take the CM varieties and algebraic correspondences in Covers Lemma 3.4, combine their supplied character determinants, and use CM Corollary 8.2 to lower degree three to degree one before mapping to B.

There is an exact obstruction **at the proposed CM-supply step**. For every CM abelian variety M, every integer j, and every algebraic correspondence

\[
\Gamma\in CH^{\dim M+j}(M\times B),
\]

the Hodge map from `H^{3−2j}(M)(−j)` to H³(B) has **zero projection to U**. Indeed, its source and image are of CM type, as are their Hodge subquotients. U is a direct sum of copies of the simple non-CM structure V(−1), and has no nonzero CM sub-Hodge structure. Compose with any Hodge projection to U and use semisimplicity. The conclusion is independent of whether the chosen projection is algebraic.

The same argument handles finite sums, products of CM sources, and their Tate twists. It is not a prohibition on tensoring CM sources with non-CM cohomology: doing that reintroduces a non-CM source and no longer meets the proposed CM-effective-realization contract. In particular, the determinants of the rank-two character spaces are trivial under their derived SL₂ factors; the desired `W₁⊗W₂⊗W₃` is nontrivial under all three. Determinant supply cannot itself be a nonzero map onto that block.

**Result of the attempt:** the accepted CM GHC theorem does not manufacture the desired algebraic realization of U. This is a direct source/image obstruction, not a finite tensor-closure calculation or a claim that every possible construction fails.

## 3. Attempt B: an explicit sixfold and phase quotient carrying a level-one block

The small cyclic-cover search from the earlier round only listed signatures. Here is an actual quotient construction and its exact cohomology, valid for **every** `t∈C\{0,1}`.

Let X be the smooth projective normalization of

\[
y^9=f_t(x),\qquad f_t(x)=x(x-1)(x-t),
\]

and let B₉ be its six-dimensional primitive Prym, equivalently the isogeny quotient of Jac(X) by the genus-one quotient `u³=f_t(x)`. Let δ be the order-nine deck transformation, and label the eigenspaces W_j using the inverse-pullback convention for which

\[
d_j=\dim W_j^{1,0}=-1+\sum_{a\in\{1,1,1,6\}}\{ja/9\}.
\]

For the primitive labels `j=1,2,4,5,7,8`, the values are respectively `0,0,1,1,2,2`; each W_j has dimension two. The primitive H¹ has dimension twelve. The coherent triples for `K=Q(ζ₃)⊂Q(ζ₉)` are `{1,4,7}` and `{2,5,8}`. Consequently

\[
U_9\otimes\mathbf C=
(W_1\wedge W_4\wedge W_7)\oplus
(W_2\wedge W_5\wedge W_8)\subset H^3(B_9,\mathbf C)
\]

is rational, has dimension sixteen, and has Hodge numbers `(h²¹,h¹²)=(8,8)`. Rationality follows because the unordered pair of triples is stable under `(Z/9)×`. The character projectors and exterior product realize this inclusion algebraically in the cohomology of curve/Jacobian powers. This is a **degree-three** realization, not a degree-one realization after a Tate twist.

Now put

\[
N=\{(a,b,c)\in(\mathbf Z/9)^3:a+4b+7c=0\},\qquad
Y_0=X^3/N.
\]

The affine function field has the concrete presentation

\[
z^9=f_t(x_1)f_t(x_2)^4f_t(x_3)^7,
\qquad z=y_1y_2^4y_3^7.
\]

A cyclic permutation of the three factors normalizes N, since it multiplies its defining character by 4 or 7. Form the projective finite quotient `Y=Y₀/C₃`.

**Exact calculation.** The annihilator of N consists of

\[
(j,4j,7j)\pmod9,\quad 0\le j<9.
\]

For j nonzero none of the three entries is zero. Since `H¹(X)^μ₉=0`, all N-invariant H³ therefore comes from three degree-one factors. For primitive j these are six summands of dimension eight. The 3-cycle permutes them in two free orbits, giving an invariant space of dimension sixteen. Its Hodge structure is exactly U₉: a 3-cycle on three odd-degree factors has positive Koszul sign. For j=3 and 6 there are two additional one-dimensional summands of types `(0,3)` and `(3,0)`. Thus

\[
h^{3,0}(Y)=h^{0,3}(Y)=1,\qquad
h^{2,1}(Y)=h^{1,2}(Y)=8,\qquad H^1(Y)=0.
\]

These statements concern the **singular finite quotient**, whose rational cohomology is the finite-group invariant part. They are not asserted as the full Hodge numbers of a resolution. The primitive projector is invariant under the cyclic permutation and is rational; it can also be represented by the usual quotient/group-algebra correspondences. The sum of Abel–Jacobi maps `X³→B₉` pulls a coherent exterior tensor back to the alternating sum of its slot permutations; N-invariance retains the three cyclic terms, which are nonzero and linearly independent across their slot summands. This explicitly identifies the nonzero U₉ carrier.

A resolution contains the pullback of this pure quotient cohomology (finite quotients of smooth varieties are rational homology manifolds, and pullback has a degree/trace left inverse). Resolution does not lower the degree of the primitive block. In particular, quotient singularities are rational, so the resolution still has irregularity zero. It does not acquire the required weight-one source merely by being resolved.

### The failed cylinder and the scope of this candidate

I tried the branch-boundary strata as supports/cylinders. Their preimages have at least one coordinate at a branch point. Restriction of the displayed tensor of three H¹ factors to every such stratum is zero: one H¹ factor restricts to a point. This is a calculation of the proposed boundary detection maps, not a proof that all interior supports vanish. The determinant argument in Covers Lemma 3.4 uses **top exterior powers of repeated identical characters** and a distinguished Abel fiber. Here the three characters are distinct; the residual eight-dimensional tensor does not become its determinant line. Replacing it by one loses precisely the desired representation.

Arapura's prime-degree normal-crossing hyperplane theorem cannot be applied to this ninth-root weighted cover of `(P¹)³`, followed by a nonabelian quotient. Its more general theorem has additional hypotheses and an extremal-Hodge-number inequality, not established here. In fact a conclusion that all positive-coniveau odd cohomology is algebraic would be incompatible with the nonzero level-one H³ just computed, so one cannot silently declare that theorem's hypotheses satisfied.

**No identification with the fixed R3 B is asserted.** The K-signature of B₉ is `(3,3)`, but this calculation alone is not a certificate of its homological determinant, its quaternion corestriction, a rational eight-dimensional descent, or equality of its period with a specified BHPS fiber. Thus this is an explicit geometric test of the proposed mechanism, not an unproved substitution of B₉ for B. Even granting those additional comparisons would leave the Tate-twisted algebraic link absent. The classical family and a finite-quotient carrier do not meet the requested novelty threshold.

## 4. Attempt C: use the actual BHPS curves to obtain a cylinder

The obvious first construction is a morphism from a BHPS genus-four curve C to B, or a degree-one correspondence from C to one of the explicit hypergeometric curves X₇,t or X₉,t, then a geometric family on B. Two exact tests rule out these initial maps at every fiber where `A=Jac(C)` is an actual Mumford fourfold.

**Four-branch degree-one exclusion.** Let X be any connected cyclic cover of P¹ with at most four branch points, and let A be a simple abelian variety of dimension at least two with `End⁰(A)=Q`. Then

\[
\operatorname{Hom}(A,\operatorname{Jac}(X))\otimes\mathbf Q=0.
\]

Proof: each nontrivial deck-character H¹ eigenspace has dimension `r_χ−2≤2`, where r_χ counts the nontrivial inertia points of its cyclic quotient; the trivial eigenspace is zero. If an A-isotypic factor Aᵐ existed, it would be preserved by the deck automorphism. On `H¹(A)⊗Qᵐ` that automorphism acts on the multiplicity space, because `End⁰(A)=Q`. Every nonzero complex eigenblock would therefore have dimension at least `2 dim A≥4`, a contradiction. This is a universal dimension proof, not extrapolation from a branch-tuple search.

It applies directly to both BHPS hypergeometric covers, independently of their conjectured higher tensor relationship. In particular their Jacobians, all their powers, and products with CM abelian varieties have no A-isogeny factor. The CM factors cannot contain A because A is non-CM.

For the fixed repaired partner B, `Hom(A,B)=0` also follows from its derived representation: H¹(B) has standard two-dimensional constituents for single SL₂ factors, while V is the tensor product of all three. Every morphism C→B is consequently constant. More generally a morphism `C×Z→B`, with Z smooth projective connected, factors through Z up to a constant, by the product formula for Albanese varieties. Its direct-image cycle family over C is constant and gives no nonzero Abel–Jacobi map to U. This excludes this particular product-incidence construction, not arbitrary families of cycles over C.

**Geometric support consequence.** Suppose a smooth resolution D̃ of a divisor in B is dominated by a product of these four-branch cyclic-cover curves and CM abelian varieties. Then H¹(D̃) injects into H¹ of that product: resolve the dominant rational map, use injectivity of H¹ under a dominant proper map, and birational invariance of H¹ of smooth projective varieties. Thus H¹(D̃) contains no V. The Gysin map `H¹(D̃)(−1)→H³(B)` has zero U-projection. Projective bundles or blowups of the source do not change this H¹ conclusion.

This is a precise obstruction to using the explicit cover-product source geometry as a divisor support. It says nothing about a new branched cover whose irregularity increases, a divisor not dominated by those products, or an unrelated irregular variety. It does not assert that all tensor constructions are geometrically impossible.

## 5. Attempt D: theta/ample-divisor support on the repaired sixfold

For every normal ample divisor D⊂B having rational singularities, and every resolution `j:D̃→D→B`,

\[
H^1(B,\mathbf Q)\xrightarrow{j^*}H^1(\widetilde D,\mathbf Q)
\quad\text{is an isomorphism},\qquad
\operatorname{pr}_Uj_*H^1(\widetilde D)(-1)=0.
\]

Proof: in `0→O_B(−D)→O_B→O_D→0`, Serre duality and Kodaira vanishing give `H¹(O_B(−D))=H²(O_B(−D))=0` since dim B=6. Hence `H¹(O_B)→H¹(O_D)` is an isomorphism. Rational singularities give `H¹(O_D)≅H¹(O_D̃)`. Hodge symmetry now makes j* an isomorphism on rational H¹. For α∈H¹(B), the projection formula gives `j_*j*α=α∪[D]`. Its U-component vanishes since there is no Hodge map from H¹(B) to U(1), by the representation comparison in §4.

Consequently smooth ample divisors, and normal ample divisors with rational singularities, cannot supply the proposed cylinder. In the principally polarized case, every irreducible theta divisor falls in this exclusion by Ein–Lazarsfeld. The R3 polarization was not assumed principal, so this last application is conditional on having that theta divisor; it is not an extra premise about B.

This is stronger than observing that a smooth theta divisor is unhelpful: resolving its rational singularities does not create the needed Albanese factor. It does **not** exclude all singular divisors. If all components of a prospective support are ample, at least one useful component must fail normality or rational singularities. No claim about every divisor of the sixfold, or all semiregular sheaves, follows.

## 6. Validation and final status

[check.py](../experiments/i02_hodge/check.py), run with `python3 -I`, independently computes the character ranks for the two actual BHPS hypergeometric covers and the degree-nine example, the 81-element kernel, its annihilator, and the cyclic-permutation invariant Hodge dimensions. Its [output](../experiments/i02_hodge/check.out) agrees with the handwritten calculation. These finite checks certify those exact identities only. The all-parameter quantifier follows from the smooth cover's fixed branching data and Chevalley–Weil; the universal degree-one exclusion and divisor obstruction have the proofs above.

Adversarial checks retained:

* The quotient has a nonzero degree-three block, not a constructed CH² class on A×B. A level-one Hodge structure defines an abelian variety up to isogeny, but that abstract Riemann construction does not algebraize its inclusion in H³.
* The two compact eigenspaces contribute Hodge index 0 and 1 to an individual tensor; their dimensions 0 and 2 are not themselves those indices. The resulting tensor types really are `(2,1)` and `(1,2)`.
* The quotient/resolution Hodge numbers are distinguished. Exceptional cohomology cannot simply be discarded.
* B₉ is not declared equal to the repaired split partner from signature alone. No BHPS conjecture was used as a theorem.
* The CM-source vanishing permits no claim about arbitrary non-CM auxiliary constructions. The divisor lemma requires ampleness and rational singularities. The product-domination lemma requires an actual dominant rational map.
* No CM-density propagation, generic-to-special promotion of the cover theorem, arbitrary-polarization KS substitution, or dimension-count proof of semiregularity was used.

**Final research status:** several actual constructions were attempted and locally replaced when their required component vanished. The explicit phase quotient is the strongest constructed object; the strongest proved target-specific statements are the CM-image, four-branch degree-one, product-supported-divisor, and normal-rational-ample-divisor obstructions. They explain why these concrete routes do not supply the missing class. They are elementary/classical-method consequences and are not relabelled as a substantial new solution. No non-CM Mumford fiber or rank-nine K3 case has been newly proved in this round.
