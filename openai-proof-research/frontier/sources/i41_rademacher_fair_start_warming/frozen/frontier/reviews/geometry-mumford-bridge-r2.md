# Mumford fourfolds: an independent bridge round (r2)

**Parent status: final review completed.** The [independent R3 audit](geometry-partner-review-r3.md) accepts repaired P/R1/R2 as a classical construction and conditional reduction, identifies exact prior art for R3, and rejects blanket rigidity, spreading and CM-KS assertions. That review supersedes conflicting formulations below. The parent reproduced all four original outputs and the independent final audit. No exceptional cycle or new solved Hodge case was produced. The balanced trace-form specialization has unverified literature novelty and is not counted as the significant new advance requested.

Research date: 2026-10-08. Upstream pin: [openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). Theorems in that revision are taken as true. Withdrawn manuscripts are not. This is an independent round after the scout `frontier/scouts/geometry.md`. None of the scout's "proved" claims are used as premises. In particular its Theorem B1 (all-powers HC ⇔ Q_f algebraic) is being audited separately, and nothing below depends on it.

Files written: this review; `frontier/experiments/geo_mumford_bridge_r2/` (four scripts and their outputs); `frontier/sources/geo_mumford_bridge_r2_lit/` (arXiv cache and README with hashes). Nothing was staged or committed, and no shared index was edited.

## 0. Bottom line

**No new case of the Hodge conjecture is proved here.** The Mumford-fourfold problem is still open after this round. What I obtained:

| ID | Statement | Kind | Novelty |
|---|---|---|---|
| **P** | Every Mumford-type fourfold A has a *partner*: an abelian sixfold B with an imaginary-quadratic action whose compatible Hermitian form is **hyperbolic of signature (3,3)**. B carries a rational Hodge isomorphism H¹(A,ℚ)⊗K ≅ U(1), where U ⊂ H³(B,ℚ) is level one. Hyperbolicity is **equivalent to Mumford's corestriction condition** Cor_{F/ℚ}(D) = 0. | Proved theorem: Hodge theory plus Hasse–Landherr arithmetic. Finite checks done. | The partner construction itself is classical (Deligne/Carayol "abelian type"). I did not find the identity "partner split ⇔ Cor D split" in the literature I checked, or the consequence that the partner lies exactly in the corpus split-sixfold range. Not certified new. |
| **R1** | Unconditionally, every Hodge class on every Aⁿ becomes algebraic after transport to B^{2p} along the Hodge isomorphism of P. Equivalently, the "Mumford block" of the homological motive of B satisfies HC in all tensor powers. | Proved corollary of P plus corpus Weil Thm 1.1. | Same status as P. It is a statement about B, not about A. |
| **R2** | HC in every codimension on every Aⁿ follows from algebraicity of **one** codimension-2 class Φ on A × B (the partner class). Φ is algebraic ⇔ the generalized Hodge conjecture holds for U ⊂ H³(B) ⇔ some family of codimension-2 cycles on B, parametrized by a curve, has Abel–Jacobi image meeting J(U) ≅ A⊗O_K nontrivially. | Proved conditional reduction. | Reduction new to this project. Its significance is limited by §5: Φ is first-order rigid in exactly the way Q_f is. |
| **R3** | HC on every Aⁿ follows from algebraicity of **one exact even-Clifford Kuga–Satake tensor** for **one** K3 surface S of Picard rank 13 with T_S ≅ Lie(Hg A) (Galluzzi). Real multiplication is **not** needed as a separate input: corpus K3 Thm 1.1 supplies it. Without the F-twist the Kuga–Satake classes close up only to a 4-dimensional space, not to all 8 dimensions. | Proved conditional reduction plus exact closure computation. | Probably **not** new. Bouchet–Hanselman–Pieper–Schiavone §5.2 state the KS + RM route. The Zenodo record of Bhattacharjee–Mandal–Bhattacharya (Oct 1 2026) claims this exact reduction "to the Kuga–Satake class of one K3 surface of Picard number thirteen". The record is unrefereed and I did not verify it. |
| **S** | Stress tests. (i) The first-order Hodge loci of Q_f in Def(A×A) and of Φ in Def(A×B) are both exactly 1-dimensional: the Mumford/Carayol curve direction. (ii) For every quadratic-field structure on A², the Weil classes are Lefschetz classes, so the eightfold route is vacuous on A² whatever the withdrawn paper says. (iii) The cyclic 7-cover realizations have the wrong signature (1,5). | Exact computations plus short proofs. | (i) agrees with the Zenodo "rigidity" claim. (ii) is classical in substance. |

**Outcome.** The partner route requires an algebraic class linking A and B; the KS route requires an exact algebraic K3-to-KS tensor. Neither was constructed. The local calculations on the partner class do not rule out other methods, and the KS tensor is not confined to the curve in its natural ambient variation. See the final audit for the precise scope.

## 1. Sources actually read and pin checks

Pinned corpus PDFs were re-downloaded from `raw.githubusercontent.com/openai/math/fd4aeeb2…/preprints/…`. Their hashes match `frontier/sources/geo_CATALOGUE.md`.

- **Weil paper** `Weil-classes-and-Hodge-classes-on-abelian-powers-October-6-2026/paper.pdf` (sha256 `c035db86…`): Thm 1.1, Thm 1.2, Lemma 2.1, §1.2.
  - **Exact contract of Thm 1.1:** E imaginary quadratic; A a complex abelian sixfold with an E-action; a compatible polarization (e(ax,y) = e(x,āy)) whose rational Hermitian form h_E(x,y) = e(x,uy) + u·e(x,y) on H₁(A,ℚ) is hyperbolic of signature (3,3). Then rational HC holds in every codimension on A^m for all m. Nonsimple varieties and special periods are included.
  - **Lemma 2.1:** CM-supply.
- **CM paper** `The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/paper.pdf` (`6e3e66a4…`): Thm 1.1 (HC for every CM abelian variety and all products and powers); §1.2–1.3 and §3, the "surface criterion": a surface S with four Hodge maps U(v_i) → H¹(S) and a nonzero quartic period yields an algebraic four-factor class.
- **K3-locus paper** `Algebraic-Kuga-Satake-correspondences-…-September-30-2026/paper.pdf` (`c9fde2b7…`):
  - **Thm 1.1 (exact):** for any projective K3 surface S, if for one rational nonisotropic w ∈ T_S, one rational polarization and one full even-Clifford realization the tensor of j_w(v)(a) = vaw is induced by a cycle in CH²(S × A²)_ℚ, then rational HC and GHC hold in every degree of every S^m.
  - **Prop 2.1:** algebraic injective F_k with algebraic left inverse R_k.
  - Thm 1.2: the V_P locus. T_S must embed in a rank-8 space, so it does **not** reach rank 9.
- **Abelian-covers paper** (Oct 6), abstract and Thm 1.1. The conclusion holds only at *tensor-Hodge-generic* points of the **full marked** variation. Mumford points are never Hodge-generic in a full family of covers, so this paper does not apply.
- **Withdrawal notices (verified, not assumed).** At the pin, the files for split abelian eightfolds (Sep 18), Kuga–Satake algebraicity for K3 (Oct 3) and products of K3 surfaces (Oct 4) are one-page ReportLab notices. I read the full text of each, via `geo_pdf/*.txt` (byte sizes 1328, 764 and 804), with hashes re-checked for the eightfold notice. Each says only that a sign error makes the signed double-point count −2m rather than 0, so the proof is unsupported. Each says it "does not assert that the mathematical statement is false". **They contain no usable theorem**, and nothing below uses them.
- **External literature.** Full texts are cached in `sources/geo_mumford_bridge_r2_lit/`.
  - **Bouchet–Hanselman–Pieper–Schiavone (BHPS),** [arXiv:2510.00093](https://arxiv.org/abs/2510.00093), *Mumford-type Shimura curves contained in the Torelli locus*. They give explicit genus-4 families C_{7,t} (hyperelliptic, triangle group Δ(2,3,7), F = ℚ(ζ₇)⁺) and C_{9,t} (Δ(2,3,9)), whose Jacobians are Mumford fourfolds.
    - §5.1: two exceptional classes δ₁, δ₂ ∈ H⁴(A²), and "products of δ₁, δ₂ and divisor classes generate the Hodge classes in H*(A²,ℚ)" [Moonen 2004, (5.9)]. **This bears on the scout's B1 novelty (A² case). Recorded here, not used as a premise. Parent integration: the independent audit subsequently identified the full all-powers theorem in H8 prior art.** They also say HC for A² is open and ask for surfaces in C⁴.
    - §5.2: the KS + RM route via Galluzzi's rank-9 K3-type structure.
  - Markman, [arXiv:2509.23079](https://arxiv.org/abs/2509.23079): CM-field secant sheaves. Semiregularity is not addressed.
  - Moonen–Zarhin (scout cache).
  - Zenodo [10.5281/zenodo.23078541](https://zenodo.org/records/23078541): verification code only; web page read, file not cached.
  - Also downloaded for scanning only: [arXiv:1810.10058](https://arxiv.org/abs/1810.10058) and [math/0103111](https://arxiv.org/abs/math/0103111).

## Governing corrections from the final audit

The complete repaired proof is [R3 §§3–7](geometry-partner-review-r3.md). The following corrections are essential when using this working report:

- Hg(A) is the tensor-product **image** of the simply connected cubic quaternionic group; its central kernel is nontrivial. The partner PEL group uses a common rational similitude multiplier. Choose the compact scalar Hodge characters and the polarization normalization explicitly, for example γ = 1/(2u), after fixing the two opposite definite signatures.
- Hyperbolicity concerns the constructed trace form. Its **raw determinant** is −N(c) modulo norms; its signed rank-six discriminant has the opposite sign. Corestriction adds local Brauer invariants; it does not multiply the numbers 0 and 1/2.
- The two-dimensional Hom assertion is for actual Mumford fourfolds with End⁰(A) = ℚ; it does not automatically extend to CM fibers. The central-character argument in the audit establishes the rational descent and excludes other tensor pieces.
- A class Γ in CH²(A×B) becomes a forward map H¹(A) → H³(B)(1) through the codimension-five correspondence pr_A^*(θ_A³)·Γ. Its adjoint is also codimension five on B×A; their composition is codimension four on A×A. The GHC equivalence requires a nonzero rational map into the U factor, not a mere torsion intersection of complex tori. J(U) is isogenous to A², not canonically equal to it.
- First-order ranks refer to polarized eightfold/tenfold ambient deformations, of dimensions 36/55. A genuine curve carrying the same flat tensor plus tangent dimension one proves local smoothness at that point; finite rank checks alone do not classify the global Hodge locus.
- Semiregularity must address the full relevant obstruction space and the entire Chern character. The rank of ambient Hodge variation does not supply that calculation. Uncountably many algebraic fibers are one sufficient spreading strategy, not a necessary condition for every possible proof.
- The KS tensor varies as a Hodge tensor in a seven-dimensional K3 period domain. Thus not every linking class is rigid off the Mumford curve. The corpus CM theorem covers CM **abelian varieties**, and alone does not prove the KS correspondence from a CM **K3**.
- R3 is already in the [immutable H8 source, `thm:mumfordks`](https://github.com/creelie/H8/blob/a80abf628c5f05236372e97dbfaa5b316463e9df/tex/sections/11c_mumford.tex#L203), with a stronger mixed-product corollary. The four-dimensional closure experiment discards information by retaining only the total adjoint projector. It does not show that the full exact KS tensor requires an independent real-multiplication hypothesis.

## 2. Setup

A *Mumford-type fourfold* is a complex abelian fourfold with End⁰(A) = ℚ and Hg(A) ≠ Sp₈. By Mumford's construction and the classification (Moonen–Zarhin Thm 0.1(iii); BHPS §2.1) there are:
- a totally real cubic field F with real places σ₁, σ₂, σ₃;
- a quaternion algebra D/F that is split at σ₁, ramified at σ₂ and σ₃, and satisfies **Cor_{F/ℚ}(D) ≅ M₈(ℚ)**;

such that Hg(A) = G₀ := Res_{F/ℚ}D¹ and V := H¹(A,ℚ) satisfies V⊗ℚ̄ = Std_{σ₁}⊗Std_{σ₂}⊗Std_{σ₃}. The Hodge cocharacter is nontrivial only on the σ₁ factor. End_Hdg(V) = ℚ.

## 3. Theorem P (the split partner)

**Theorem P.** Let A be of Mumford type with data (F, D). Let K = ℚ(√−d) be any imaginary quadratic field such that L := FK splits D. Such K exist, infinitely many. Then there is a complex abelian sixfold B with the following properties.
1. L ↪ End⁰(B). In particular K acts. H¹(B,ℚ) = W is free of rank 2 over L.
2. Choose the extensions ρ_i of σ_i that restrict to a fixed embedding τ of K. Then the eigenspaces W_{ρ_i} have Hodge numbers (1,1), (2,0), (0,2) for i = 1, 2, 3. So the K-signature is (3,3).
3. B has a compatible polarization whose K-Hermitian form h_K is **hyperbolic**. Here hyperbolic ⇔ disc(h_K) ≡ −1 in ℚ^×/N(K^×) ⇔ **Cor_{F/ℚ}(D) = 0 in Br(ℚ)**, which holds by the Mumford hypothesis.
4. The derived group of Hg(B) is G₀.
5. Define U := ⊕_{τ′∈Hom(K,ℂ)} ⊗_{ρ|τ′} W_ρ ⊂ ∧³W ⊗ ℂ. This is defined over ℚ, and it is a sub-Hodge structure of H³(B,ℚ) with types (2,1)⁸ and (1,2)⁸. There is a G₀-equivariant isomorphism of rational Hodge structures ψ: V⊗_ℚK ⥲ U(1).
6. Hom_Hdg(V, H³(B,ℚ)(1)) = ψ∘K, which is 2-dimensional over ℚ.

Consequently the corpus Weil Thm 1.1 applies to B: rational HC holds on every B^m.

**Proof.**

*(a) Choice of K.* For each prime p below Ram_f(D), choose a quadratic extension K_p/ℚ_p not contained in any F_v with v | p and v ∈ Ram(D). This is possible: F_v has degree ≤ 3, so it contains at most one quadratic extension of ℚ_p, and ℚ_p has at least 3 of them. Then F_v ⊗ K_p is a field, so L_v is a field and splits D_v. At the real places D_{σ₂}, D_{σ₃} ≅ ℍ is split by ℂ = L_{σ}. A global imaginary quadratic K with these finitely many prescribed completions exists by weak approximation and Krasner's lemma. By Albert–Brauer–Hasse–Noether, L splits D, so L ↪ D.

*(b) Unitary model of G₀.* Write D = (L/F, c) with c ∈ F^×; c is determined modulo N_{L/F}(L^×). Let H := ⟨1, −c⟩ be the 2-dimensional L/F-Hermitian form. Then SU(H) ≅ D¹. The standard check is: SU(⟨a,b⟩) ≅ (L/F, −ab)¹. Test cases: ⟨1,1⟩ over ℂ/ℝ gives SU(2) = ℍ¹ = (−1,−1)¹, and ⟨1,−1⟩ gives SU(1,1) = SL₂(ℝ) = (−1,1)¹.

Since L = F(√−d) with −d ≪ 0, D is ramified at σ_i ⇔ σ_i(c) < 0 ⇔ H is definite at σ_i. So H is indefinite at σ₁ and definite at σ₂, σ₃. Rescaling H by λ ∈ F^× with sign pattern (·,±,±) leaves SU(H) and disc H mod squares unchanged. This makes H positive at ρ₂ and negative at ρ₃.

*(c) PEL datum.* Put W := L² with Hermitian form H. Choose γ ∈ L with γ̄ = −γ and set e(x,y) := Tr_{L/ℚ}(γH(x,y)), which is alternating and L-compatible. The group GU(W,H) with this e is a PEL unitary datum whose Hodge numbers are dictated by the signatures of the F-valued form 2uγ·H (u = √−d) at the ρ_i. With the signs fixed in (b), they are (1,1), (2,0), (0,2).

The symmetric domain is the upper half plane coming from the σ₁ factor SU(1,1) ≅ SL₂(ℝ). The derived group is SU(H) = G₀. Choose the point of this domain equal to the image of h_A in G₀^{ad}(ℝ) = PGL₂(ℝ) × SO₃ × SO₃. Both h_A and h_B are trivial on the compact factors, since at σ₂ and σ₃ h_B acts by scalars z and z̄. The resulting polarized weight-one Hodge structure is H¹(B) of an abelian sixfold B. This gives (1), (2) and (4).

*(d) Hyperbolicity, which is item (3).* Set w := Tr_{L/K}(γH). Then Tr_{L/ℚ}(γuH) = u(w − w̄) and u·Tr_{L/ℚ}(γH) = u(w + w̄), so
  h_K(x,y) = e(x,uy) + u·e(x,y) = 2u·Tr_{L/K}(γH(x,y)) = Tr_{L/K}(δH(x,y)),  δ := 2uγ ∈ F^×.

Diagonalize H = ⟨a₁, a₂⟩ and pick a ℚ-basis {f_k} of F; this is also a K-basis of L. The Gram matrix of h_K is ⊕_i (Tr_{F/ℚ}(δa_i f_k f_l))_{k,l}. Its determinant is N(δa₁)N(δa₂)d_F², so
  disc h_K ≡ N_{F/ℚ}(disc H) = N_{F/ℚ}(−c) = −N_{F/ℚ}(c)  (mod ℚ^{×2} ⊂ N K^×).

This identity is checked exactly for F = ℚ(ζ₇)⁺ in `partner_checks.out`, together with d_F = 49.

By Landherr, a K/ℚ-Hermitian space of signature (3,3) is hyperbolic iff its discriminant is ≡ (−1)³. So h_K is hyperbolic ⇔ N_{F/ℚ}(c) ∈ N_{K/ℚ}(K^×). By the Hasse norm theorem for the quadratic extension K/ℚ and the projection formula (−d, N_{F/ℚ}c)_p = ∏_{v|p}(−d, c)_{F_v} = ∏_{v|p} inv_v(D), this is equivalent to: for every p, the sum over v | p of inv_v(D) vanishes. That is exactly the vanishing of Cor_{F/ℚ}(D) at every finite p. At ∞ the product is (+)(−)(−) = +, automatically.

The class of the dual form (on H₁ rather than H¹) differs by a square, so the corpus convention is met. The polarization is compatible: e(ax,y) = e(x,āy) for a ∈ K ⊂ L. So B satisfies the exact hypotheses of corpus Weil Thm 1.1.

*(e) The level-one block, which is items (5) and (6).* The set of "coherent" triples {(ρ₁,ρ₂,ρ₃) : all ρ_i|_K = τ′} is stable under Aut(ℂ). Each W_ρ is a sub-ℂ-Hodge structure, because L acts by Hodge endomorphisms. So U is a rational sub-Hodge structure of ∧³_ℚW = H³(B,ℚ); it sits inside ∧³_K W.

Hodge types: on U_τ the cocharacter is h_U(z) = (zz̄)·(diag(z,z̄) ⊗ 1 ⊗ 1), because W_{ρ₂} has scalar z and W_{ρ₃} has scalar z̄. That is a Tate twist of h_A. So U(1)_τ ≅ V_ℂ as real Hodge structures with G₀(ℝ)-action. Over K, U and V⊗K are two K-forms of the same absolutely irreducible G₀-representation, so they are isomorphic. Since both Hodge structures are given by the same element of G₀(ℝ)·ℝ^×, any G₀-isomorphism ψ is a Hodge isomorphism after the twist. This gives (5).

For (6): the V-isotypic part of H³(B) consists of the 8 one-from-each-σ pieces. A rational Hodge morphism from V must be supported on a Galois-stable set of pieces carrying the Hodge cocharacter of V(−1).
- `partner_checks.out` shows that the level-one pieces are rrr, bbb, brr and rbb. The σ₁ choice is irrelevant because both ρ₁ and ρ̄₁ have type (1,1).
- The Galois orbit of brr also contains rbr, which is not level one, because Galois acts transitively on the σ_i.
- So only the coherent pair {rrr, bbb} = U is admissible. Hence Hom_Hdg(V, H³(B)(1)) = Hom_{G₀}(V, U(1))^{Hdg} = End_Hdg(V)⊗K = K. ∎

*Remark (non-split case).* If Cor_{F/ℚ}D ≠ 0, then (d) shows that the partner is a **non-split** Weil sixfold, outside corpus Thm 1.1. This is consistent with V being 16-dimensional (a Mumford-type eightfold) in that case. Mumford's condition is thus exactly the condition under which the corpus split-sixfold theorem reaches the partner.

*Remark (explicit partner for BHPS).* For BHPS's X₇, D is the Δ(2,3,7) quaternion algebra over ℚ(ζ₇)⁺, ramified only at the two real places. Every imaginary quadratic K works, for example K = ℚ(√−7) with L = ℚ(ζ₇). Four-point cyclic 7-covers of ℙ¹ do **not** realize the partner: their residue-embedding Hodge sum is always 1 or 5 (`cyclic_search.out`, the N = 7 rows), giving signature (1,5) rather than (3,3).

## 4. Consequences

**R1 (unconditional).** Let ξ be a rational Hodge class on Aⁿ. Lift it, by the standard antisymmetrization (Weil paper §1.2/§2.4), to Hodge tensors in V^{⊗2p}. Then (ψ∘k)^{⊗2p}(ξ) is a rational Hodge class in the Künneth component H³(B)^{⊗2p} of B^{2p}. It is therefore algebraic by corpus Weil Thm 1.1. In particular the image of Q_f in U^{⊗4} ⊂ H¹²(B⁴) is algebraic.

*Significance:* the only thing missing for A is the link from A to B.

**R2 (conditional reduction).** Suppose some Γ ∈ CH²(A×B)_ℚ has nonzero Künneth component in H¹(A)⊗H³(B). Then rational HC holds in every codimension on Aⁿ for every n.

*Proof.*
1. Künneth projectors and the inverse Lefschetz operator Λ are algebraic on abelian varieties (Deninger–Murre; Lieberman). So Γ yields an algebraic Hodge map φ: H¹(A) → H³(B)(1), which is nonzero. By P(6), φ = ψ∘k with k ≠ 0.
2. Let φ^♯ be the adjoint with respect to the polarization forms. It is algebraic (transpose plus Lefschetz operators). φ^♯φ ∈ End_Hdg H¹(A) = ℚ is a scalar c.
3. c ≠ 0: φ(V) is a sub-Hodge structure of H³_prim(B). It is primitive because L·H¹(B) is not V-isotypic. By Hodge–Riemann the polarization restricts nondegenerately to φ(V).
4. For a Hodge tensor ξ ∈ V^{⊗2p}: φ^{⊗2p}ξ is algebraic on B^{2p} by corpus Thm 1.1. So ξ = c^{−2p}(φ^♯)^{⊗2p}φ^{⊗2p}ξ is algebraic, and diagonal pullback returns the class on Aⁿ. ∎

*Equivalent forms of the hypothesis.*
- (⇒ GHC) Restrict H¹(A) to a curve C ⊂ A (Lefschetz). The correspondence becomes Z ∈ CH²(C×B), of dimension 5, so its image lies in N¹H³(B). Hence U = φ(V)⊗K ⊂ N¹H³.
- (⇐) Suppose U ⊂ N¹. Then U is a quotient of the Gysin image of H¹(D̃) for some divisor D ⊂ B. A Hodge section H¹(A) → H¹(D̃) is induced by a homomorphism into Pic⁰, so it is algebraic, and composing with Gysin gives Γ.
- **Concretely for BHPS Jacobians** A = J(C_{7,t}): one needs a family {Z_c}_{c∈C} of codimension-2 cycles on B_t whose Abel–Jacobi map J(C) → J²(B_t) is nonzero. Its image then lies in J(U) ≅ A⊗O_K. Equivalently, one needs a 5-dimensional cycle in C × B with a nonzero H¹(C)⊗H³(B) component.

*Novelty and significance.* R2 is a conditional reduction. Its substance is P, which puts the partner inside the corpus range. It does **not** make the problem easier by itself: compare S(i).

**R3 (Kuga–Satake form).**
- *Statement.* Let S be a projective K3 surface with T_S ≅ T := Lie(Hg A) up to rational scaling of the form. T has rank 9, signature (2,7), and RM by F (Galluzzi; BHPS §5.2). Such S exists:
  - T ⊥ N ≅ Λ_ℚ, with N of rank 13, is solvable;
  - Nikulin 1.12.3 applies, since 9 + 9 < 22;
  - Torelli plus surjectivity give a surface with ρ = 13, using that T is irreducible.

  KS(S) ~ A^{32} by Galluzzi; I used this via BHPS and did not re-derive it. If the j_w-tensor of S is algebraic for one w, then HC holds on every Aⁿ.
- *Proof.*
  1. Corpus K3 Thm 1.1 gives HC on all S^m. In particular the F-action m_f on T is algebraic on S × S. **This is the point: RM need not be assumed.**
  2. Corpus Prop 2.1 gives an algebraic ι: T → End(W) with an algebraic left inverse R. The image of ι lies in 𝔤⊗End(M), where W = V⊗M.
  3. Compose ι∘m_f∘R with the algebraic block projections coming from the isogeny KS ~ A^{32}. This produces the F-twisted projectors p_f = Σ_iσ_i(f)p_i onto S_i ⊂ Sym²V in End(V⊗V). They are Hodge classes on A⁴, and they are algebraic.
  4. `closure_pf.out` (exact arithmetic) shows that Lefschetz {aaa, bbb, ddd} together with p₁, p₂, p₃ close under composition and S₄ leg permutations to all of Inv_{G₀}(V^{⊗4}), which is 8-dimensional.
  5. The rest is the same multilinear and descent argument as in R2.
- *Necessity of the F-twist.* Lefschetz plus P_T = p₁+p₂+p₃ closes at **4**. This describes the information retained by P_T alone. It does not describe everything obtainable from the full KS tensor, whose blocks supply further data. Lefschetz plus a single p₁ closes at 6.
- *Novelty:* probably not new (see §0). The idea is short once corpus K3 Thm 1.1 is accepted. The obstruction is that no KS tensor is known algebraic for a rank-9 T: V_P has rank 8, and Floccari's locus has rank ≤ 6.

## 5. Stress tests

**S(i) Variational and semiregularity rigidity (exact computation, `hodge_locus.out`).** Model the Hodge decompositions over the rational basis adapted to V^{1,0} = e₊⊗V₂⊗V₃. Compute the first-order Hodge locus, ker(ξ ↦ D_ξT), over polarized deformations.

| Class | dim Def (polarized) | rank | first-order Hodge locus |
|---|---|---|---|
| Q_f on A×A (f₁, f₂, f₃ distinct) | 36 | 35 | **1** |
| Φ on A×B | 55 | 54 | **1** |
| sanity: θ₁·θ₂ | 36 | 16 | 20 (product deformations) |
| sanity: q₁+q₂+q₃ (Lefschetz) | 36 | 26 | 10 (diagonal deformations) |

The finite model computations give a one-dimensional tangent kernel for both displayed tensors. Identifying the full Hodge locus and proving its reducedness requires a separate geometric argument; the computation alone does not establish those claims. Consequences:
- **CM density alone is insufficient.** The algebraic locus of a flat Hodge class is a countable union of closed subvarieties of the curve. Countably many CM points do not force any cycle-parameter component to dominate the curve. Even one additional non-CM point is insufficient for this argument; uncountably many points, or a separate deformation/propagation theorem, would be needed.
- **A semiregular seed** Z (an lci cycle, or a sheaf with Buchweitz–Flenner semiregularity) would need its obstruction space to absorb a rank-35 (resp. 54) image injectively. This is no contradiction, but it means a seed must be special to the curve. Any cycle defined uniformly over a family whose generic Mumford–Tate group is Sp has a Lefschetz class, since pushforward and pullback along homomorphisms preserve Lefschetz-group invariants. So no "universal" construction (Abel–Prym curves, sums and differences of Lefschetz curves, homomorphism images) can work.
- The Weil paper's seed, an Abel-orbit ideal sheaf on a genus-3 Jacobian, deforms over a 9-dimensional Weil domain. The Mumford classes have no such domain: the Hodge locus is the 1-dimensional curve.

**S(ii) The eightfold route is vacuous on A².** For any unital K ↪ End⁰(A²) = M₂(ℚ), Sp(V) acts K-linearly on H¹(A²) = V⊗ℚ² with det_K = 1. So the Weil classes ∧⁸_K H¹(A²) are invariants of the Lefschetz group Sp(V), hence Lefschetz classes (Murty; Milne, *Lefschetz classes on abelian varieties*, 1999). So even a correct split-eightfold theorem could not give Q_f through a K-structure on A². The scout's mention of the Serre tensor A⊗O_K is therefore a dead route independently of the withdrawal. Relevant 8-dimensional Weil-type objects would have to be partners, not A².

**S(iii) Surface criterion (corpus CM §3) for Mumford.** A surface S with Hom(Alb S, A) of rank ≥ 2 gives algebraic quartic forms in Inv(V^{⊗4}). Their Albanese link is automatically algebraic. They are non-Lefschetz only if the cup product ∧²(V⊗M) → H²(S) sees an F-twist on the S_i. Products of curves give products of pairings, which are Lefschetz. Surfaces inside A² are circular. Shimura surfaces of unitary or quaternionic type have Albanese factors of GL₂- or CM-type, never End = ℚ Mumford factors; this is a heuristic, not proved here. BHPS ask exactly for such surfaces in C⁴. **No candidate was found.**

## 6. Precise obstruction and what would close it

Any one of the following closes HC on all powers of a given Mumford fourfold:
- (Φ) one codimension-2 cycle on A × B with nonzero H¹⊗H³ component; equivalently GHC for the level-one block U of the split partner (R2);
- (KS) one exact even-Clifford KS tensor for one Galluzzi K3 surface of Picard rank 13 (R3);
- (Q) Q_f itself, via the scout's B1 or Moonen's (5.9) for A².

These are sufficient hypotheses, none constructed here. At compatible CM abelian fibers the corpus CM theorem covers the partner and exceptional classes, but does not alone cover the K3-to-KS class. Semiregular deformation and uncountably many algebraic fibers are possible strategies, not an exhaustive list or a proved requirement.

The most concrete form found is for BHPS's explicit genus-4 curves C_{7,t}: **find a family of codimension-2 cycles on the explicit split partner B_t, parametrized by C_{7,t}, with nonzero Abel–Jacobi image.** By P, R1 and R2, that alone would prove HC on every power of J(C_{7,t}). I could not construct it.

## 7. Validation and reproducibility

Everything uses the Python standard library with exact `Fraction` arithmetic. Run with `python3 -I` from `frontier/experiments/geo_mumford_bridge_r2/`.
- `partner_checks.py` / `.out`: the Hodge types of the 8 tensor pieces (only rrr, bbb, brr, rbb are level one); the trace-transfer determinant identity for ℚ(ζ₇)⁺ (5/5 exact matches, d_F = 49).
- `closure_pf.py` / `.out`: an independent re-implementation of the leg-permutation and composition closure. Lefschetz alone gives 3; with p₁..p₃, 8; with P_T, 4; with p₁, 6; with q₁..q₃, 8, reproducing the scout's number independently. Idempotence of all projectors and their resolution of the identity are asserted.
- `hodge_locus.py` / `.out`: first-order Hodge loci, with the table in S(i) and both sanity rows.
- `cyclic_search.py` / `.out`: 4-point cyclic covers for N ∈ {7, 9, 14, 18} with one indefinite pair. The N = 7 rows show residue sums 1 and 5.

These are finite-algebra checks. The arguments in §§3–4 are the proofs. The arithmetic in P(d) rests on standard facts (Landherr's classification, the Hasse norm theorem, the norm-residue projection formula), which are not re-proved.

## 8. Novelty and significance, honestly

- **P:** I believe the equivalence "partner Hermitian form hyperbolic ⇔ Cor_{F/ℚ}D split" and its consequence (the partner lies in Markman's and the corpus's split-sixfold range) are not stated in BHPS, Moonen–Zarhin, Galluzzi (via BHPS), Markman 2509.23079, or the Zenodo record's description. Searches on the partner and "split Hermitian" found nothing. **Not certified new**: this is a specialist check, and the Deligne/Carayol partner itself is classical.
- **R1 and R2:** new to this project, as consequences of P. They relocate the problem without solving it, and S(i) shows the relocated class is as rigid as the original.
- **R3:** likely already claimed (Zenodo) and anticipated (BHPS §5.2).
- **No claim** of a new case of the Hodge conjecture. MathDB #315851 (Hodge, landmark) and #397798 (named) are not advanced beyond the conditional statements above.
