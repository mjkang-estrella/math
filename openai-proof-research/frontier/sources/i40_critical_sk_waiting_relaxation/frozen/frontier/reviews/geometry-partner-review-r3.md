# Final adversarial review of the Mumford partner bridge (R3)

Date: 2026-10-08. Target: `geometry-mumford-bridge-r2.md`, particularly P, R1, R2 and the stress-test conclusions. I read `openai-proof-research/AGENTS.md`, the pin/catalogue and the two independent R2 reviews. Actual theorems at OpenAI/math **fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** are premises; withdrawal notices supply no theorem. No nested agents, shared edits, staging or commits. My writes are this report and the `geo_partner_review_r3` source/experiment directories.

**Parent integration:** nine successful primary-download hashes and all 37 immutable H8 source hashes verified. The independent `check.py` output was reproduced exactly, including central-character and partner-rank checks. The primary H8 theorem and mixed-product corollary were inspected. The bridge report now carries the governing repairs; the research outcome records no significant new solved Hodge case.

## 1. Verdict

**Accept a repaired split-partner theorem and its conditional cycle reduction. Reject promotion to a new solved Hodge case, reject the blanket rigidity conclusion, and substantially revise the novelty assessment.**

The strongest justified statement is the following. Let A be an **actual** Mumford fourfold, with End⁰(A)=Q and actual Hodge group the tensor-product image of the usual cubic quaternionic group. For every imaginary quadratic K such that FK splits its quaternion algebra D, there is a polarized abelian sixfold B with K-action, split homological Hermitian form of signature (3,3), and a rational sub-Hodge structure

    U ⊂ H³(B,Q),             U(1) ≅ H¹(A,Q) ⊗Q K.

Such K exist infinitely often. For this B and this period,

    dimQ Hom_Hdg(H¹(A),H³(B)(1)) = 2.

The determinant/corestriction assertion is correct **for the constructed trace form**, with determinant conventions fixed below. Corpus Weil Theorem 1.1 therefore proves HC on every power of B. If **one nonzero** class in

    [H¹(A,Q) ⊗ H³(B,Q)](2)

is algebraic, then HC holds on every power of A. Existence of such a class as an algebraic cycle is equivalent to U⊂N¹H³(B,Q), the GHC assertion for this block. The algebraic class has not been constructed.

R1 is a correct transport statement about classes on powers of B, with the twists restored. It does not imply algebraicity of the transporting Hodge correspondence. R3 can be retained as an **already public conditional theorem**, after replacing its abbreviated proof by the argument in §7; the full immutable H8 source already contains a stronger version. No genuinely new solved case of the high-importance MathDB Hodge target results.

## 2. Source contracts and bounded prior-art audit

### 2.1 Accepted corpus

I downloaded the actual pinned PDFs anew. URLs, byte sizes and SHA-256 hashes are in [manifest.json](../sources/geo_partner_review_r3/manifest.json). The relevant exact contracts are:

* [Weil paper](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weil-classes-and-Hodge-classes-on-abelian-powers-October-6-2026/paper.pdf), Theorem 1.1: a complex abelian **sixfold**, a unital imaginary-quadratic action, and an **actual compatible polarization whose homological Hermitian form is hyperbolic of signature (3,3)** imply rational HC in every codimension on every self-power. Equal complex multiplicities alone are insufficient. Special periods and nonsimple varieties are included. No GHC assertion for U is supplied by this theorem.
* [K3 quadratic-locus paper](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Algebraic-Kuga-Satake-correspondences-and-Hodge-conjectures-on-a-K3-quadratic-locus-September-30-2026/paper.pdf), Theorem 1.1: algebraicity of one **specified full even-Clifford** tensor j_w(v)(a)=vaw, for one rational nonisotropic w and one rational polarization, gives HC/GHC on all self-powers of that K3. Theorem 1.2 requires embedding its actual transcendental quadratic space in the rank-8 V_P, hence does not supply this tensor for rank 9. Proposition 2.1 supplies an algebraic left inverse to the specified map; an arbitrary embedding cannot silently replace it.
* [CM paper](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/paper.pdf), Theorem 1.1: HC for CM **abelian varieties**, including their products and powers. This does not by itself prove the Kuga–Satake correspondence from a CM **K3 surface**.

I also read the complete cached texts of the three pinned withdrawal notices identified by the independent R2 reviews: split eightfolds, general KS algebraicity, and products of K3 surfaces. They contain no surviving positive theorem. No archived pre-withdrawal claim is used here.

### 2.2 Full primary H8 source, not a Zenodo description

I fetched all 37 nonfigure TeX manuscript files at **creelie/H8 a80abf628c5f05236372e97dbfaa5b316463e9df**, including the complete Mumford and rigidity sections. [h8_manifest.json](../sources/geo_partner_review_r3/h8_manifest.json) records every immutable raw URL and hash. I searched the full retrieved manuscript for partner/unitary/sixfold/half-twist/corestriction terminology and read the relevant arguments. The October 2 public release had already been checked in R2; I use the immutable manuscript for the mathematics.

Decisive overlaps in [11c_mumford.tex](https://raw.githubusercontent.com/creelie/H8/a80abf628c5f05236372e97dbfaa5b316463e9df/tex/sections/11c_mumford.tex):

* `thm:mumfordpowers`, beginning line 543, is the known all-powers reduction. It needs no new research round or reproof here.
* **`thm:mumfordks`, beginning line 203**, proves existence of the Picard-rank-13 K3, KS isogeny to A³², and the conditional algebraicity of real multiplication and exceptional classes. Its Clifford-block argument explicitly produces the real multiplication; it is not merely a record abstract.
* **`cor:mumfordksproducts`, beginning line 735**, gives HC for all mixed Sᵃ×Aᵇ under that KS hypothesis, stronger than the bridge's stated R3.
* **`rem:mumfordunitary`, beginning line 893**, already discusses PEL abelian sixfolds associated to the quaternion algebra and a CM quadratic extension of F, and their H² carrier of the rank-9 adjoint Hodge structure. Its signatures are (2,0),(2,0),(1,1), rather than the balanced partner's (2,0),(0,2),(1,1). It does not in that passage state the present H³-block plus split-determinant assertion.
* **`rem:mumfordkscm`** distinguishes the CM K3 issue from CM algebraicity on abelian varieties.

Moreover [11d_mumfordrigid.tex](https://raw.githubusercontent.com/creelie/H8/a80abf628c5f05236372e97dbfaa5b316463e9df/tex/sections/11d_mumfordrigid.tex), around lines 367–374, explicitly observes that the KS tensor stays Hodge on a **seven-dimensional** K3 period domain. This directly contradicts the bridge's final assertion that every linking class only stays Hodge on the curve, if applied to KS with its natural ambient variation.

These are public source/preprint statements, not assertions of peer review or earliest priority. The bridge's “probably already claimed in the Zenodo record; not verified” must be replaced by an exact primary-source attribution for R3.

### 2.3 Classical construction and bounded search limits

Primary texts inspected:

* Deligne, [*Travaux de Shimura*](https://www.numdam.org/item/SB_1970-1971__13__123_0.pdf), §§6.1–6.4: quaternionic data, adjoining a totally imaginary quadratic extension, and modifying the central Hodge action to obtain a modular construction.
* Carayol, [*Sur la mauvaise réduction des courbes de Shimura*](https://www.numdam.org/item/CM_1986__59_2_151_0.pdf), §§2.1–2.3: auxiliary imaginary quadratic extension, common rational similitude multiplier, alternating trace pairing, positivity and the associated abelian moduli problem. His displayed representation uses a larger algebra module; cite it as the classical method, not as a verbatim statement of this particular six-dimensional partner theorem.
* Van Geemen, [*Half twists of Hodge structures of CM-type*](https://arxiv.org/pdf/math/0008076v1), Proposition 2.8 and §§2.9–2.11: the precise CM-character twist, realization in a tensor product with CM H¹, and polarization. These results explain why matching derived representations without checking the central character is inadequate. They do not themselves assert algebraicity of the present A-to-B link.
* Gross, [*Incoherent definite spaces and Shimura varieties*](https://people.math.harvard.edu/~gross/preprints/incoherent.pdf), §3 and Theorem 3.1: Hermitian dimension, determinant modulo norms, real signatures, local classification and the local-global theorem. This was read through the browser; direct cache retrieval returned HTTP 403, recorded in the manifest.
* The full previously cached BHPS [arXiv:2510.00093](https://arxiv.org/abs/2510.00093), especially §§2.1, 5.1–5.2, and the relevant Hermitian discussion in Markman [arXiv:2509.23079](https://arxiv.org/abs/2509.23079), were also checked.

The focused searches covered Mumford/sixfold/Weil/partner, corestriction/hyperbolic Hermitian, Deligne/Carayol and van Geemen half twists. **I did not locate an exact prior statement of the balanced trace-form specialization in the passages inspected. That is a bounded-search observation, not evidence of absence from the literature.** The sixfold construction is classical in substance, the determinant calculation is a standard transfer/projection-formula calculation, and R1/R2 are formal consequences once the partner is supplied. None is certified substantive new mathematics. The earlier similitude claim remains subject to the Varesco prior-art finding in the independent K3 review.

## 3. P: arithmetic and polarization

Use Q(1) of weight −2. Let F be totally real cubic and D/F quaternionic, split at σ₁ and ramified at σ₂,σ₃. Put

    G̃ = ResF/Q D¹.

For an actual Mumford fourfold, CorF/Q[D]=0 and the rational eight-dimensional tensor representation r has

    Hg(A) = r(G̃),
    ker(r)Qbar = { (ε₁,ε₂,ε₃) ∈ {±1}³ : ε₁ε₂ε₃=1 }.

Thus the setup's literal equality Hg(A)=G̃ is false; it is the image of the simply connected cover. MT(A) also contains the weight torus. Use these distinctions throughout. They do not invalidate the partner.

### 3.1 A single global quadratic K really exists

For each rational p below finite ramification of D, the local degree partition of F⊗Q_p is one of

    3,       2+1,       1+1+1.

Consequently, among **all** F_v with v|p there is at most one quadratic extension of Q_p that can be a subfield of any F_v: it can only be the degree-two factor in the middle partition. Choose a quadratic field K_p/Q_p different from it. At odd p there are three nontrivial squareclasses defining quadratic extensions; at p=2 there are seven. Therefore this simultaneous choice is possible. This fills the bridge's small gap: “each completion excludes at most one” would not suffice without bounding the union of exclusions.

For every ramified v, F_vK_p/F_v has degree two, so restriction multiplies inv_v(D)=1/2 by two and kills it. At infinity, an imaginary K supplies C and splits both Hamilton factors. Choose a negative rational squareclass with these finitely many local squareclasses by weak approximation; squareclasses are open locally. K=Q(√a) has the required completions. ABHN then proves D⊗F FK is split. There is no Grunwald–Wang obstruction for this elementary quadratic squareclass construction. Infinitely many choices follow by additionally prescribing odd valuation at a new prime outside the previous finitely many discriminants and repeating.

A degree-two splitting field of a quaternion division algebra embeds as a maximal subfield. Thus L=FK embeds in D, and

    D ≅ (L/F,c) = (−d,c)F,       K=Q(u), u²=−d,

for some c∈F×. The corestriction hypothesis imposes further parity constraints on finite ramification, but is not needed for this existence argument.

### 3.2 The signs are attainable; specify the PEL group correctly

Let H=λ⟨1,−c⟩ on L², conjugate-linear in its first variable. Then SU(H)≅D¹: the corresponding quaternion symbol is (L/F,c), unchanged by λ because λ² is a norm. At σ₁ this form is indefinite; at σ₂,σ₃ it is definite. Weak approximation in F allows λ with positive sign at σ₂ and negative sign at σ₃ (and either desired sign at σ₁). Hence arrange signatures

    (1,1), (2,0), (0,2).

An arbitrary subsequently chosen γ could undo this choice. A clean normalization is

    γ = 1/(2u),      e(x,y)=TrL/Q(γH(x,y)).

This is nondegenerate, alternating, and satisfies e(ax,y)=e(x,āy) for a∈L. Choose the positive and negative Hodge subspaces at each real factor, with the noncompact period corresponding to A. This is the usual polarized unitary weight-one datum. Reversing the homology/cohomology convention reverses the associated choices simultaneously; it causes no existence obstruction. An integral lattice after clearing denominators gives an abelian variety up to isogeny, of dimension 12/2=6. No principal-polarization or integral-unimodularity claim is required.

The group acting by symplectic similitudes is the subgroup of ResF/Q GU(H) whose multiplier lies in **Q×**, not the entire group with independent F× multipliers. Its derived group is G̃. Fixing the same adjoint period alone would not determine a Hodge structure: the compact scalar actions must be z at one definite factor and z̄ at the other. Those are part of this construction.

The cohomological construction can be dualized to homology with its induced Riemann form. Hyperbolicity is preserved under the resulting Hermitian duality, conjugation and nonzero rational scaling. Thus the corpus's **homological** contract is satisfied, not just an abstract cohomological signature statement.

### 3.3 Determinant, norm and corestriction: correct iff

For general pure-imaginary γ, write δ=2uγ∈F× and set

    hK(x,y)=e(x,uy)+u e(x,y)=TrL/K(δH(x,y)).

Here the formula is with the stated conjugate-first convention. The chosen normalization gives δ=1. If H=⟨a₁,a₂⟩ and {f_j} is a rational basis of F, the two 3×3 Gram blocks are

    (TrF/Q(δ a_i f_j f_k))j,k.

Let ΔF=det(TrF/Q(f_j f_k)). The transfer determinant is exactly

    det(hK)=ΔF² NF/Q(δ)² NF/Q(a₁a₂).

Since a₁a₂=−λ²c, its class in Q×/NK/Q(K×) is **−NF/Q(c)**. All discarded factors are rational squares, hence norms. Use the word **determinant**, or define “discriminant” explicitly: the signed rank-six discriminant is −det(hK), and its hyperbolic value is +1, whereas the raw determinant's hyperbolic value is −1. Mixing these conventions would reverse the test.

Given signature (3,3), local Hermitian classification and Hasse–Landherr imply

    hK hyperbolic
      ⇔ det(hK) ≡ −1 modulo NK/Q(K×)
      ⇔ NF/Q(c) ∈ NK/Q(K×).

There is no further independent finite Hasse invariant for Hermitian spaces over a quadratic extension. On the other hand, the projection formula gives an equality of **Brauer classes**

    CorF/Q[(−d,c)F] = [(−d,NF/Q(c))Q].

A quadratic cyclic algebra (K/Q,b) splits exactly when b is a norm. Therefore the last displayed norm condition is equivalent to CorF/Q[D]=0. Equivalently, at each rational place p,

    inv_p(Cor D)=Σv|p inv_v(D)  in Q/Z,

or, in signs, the Hilbert symbol of (−d,Nc) equals the **product of Hilbert-symbol signs** at v|p. The bridge's written product of `inv_v(D)` is erroneous notation: invariants 0 and 1/2 are added, not multiplied. At infinity the two ramified places contribute 1/2+1/2=0. This verifies every place, including p=2 and primes ramified in F or K.

The iff is about this specified trace construction with opposite signs on the two definite factors. It is not an assertion that arbitrary Hermitian forms of the same signature, or arbitrary partner constructions, have that determinant. In the nonzero-corestriction case the same balanced trace form is nonsplit; this does not contradict any existence statement about unrelated varieties.

## 4. P: descent, the central character, and the exact Hom space

### 4.1 Rational descent of U and cancellation of the character

Write W=H¹(B,Q). For each embedding τ of K choose the three extensions ρ_i to L over σ_i. Inside Λ³W_C take

    U_C = ⊕τ (Wρ₁ ⊗ Wρ₂ ⊗ Wρ₃).

The summands are embedded by exterior product of the three distinct eigenspaces. The coherent triples are Galois-stable, so U is defined over Q; L acts by Hodge endomorphisms, so U is a sub-Hodge structure. Its two complex summands have dimension eight, each with Hodge numbers (4,4) in bidegrees (2,1),(1,2). Thus dimQ U=16 and its total Hodge numbers are (8,8).

As a G̃_K-representation one coherent summand is the tensor product of the three standard representations. Corestriction splitting supplies V_K, V=H¹(A,Q), as its rationally descended eight-dimensional form. The two K-representations are isomorphic: their intertwiner space commutes with scalar extension and is one-dimensional over K; a nonzero intertwiner is an isomorphism. Merely saying “two forms of an irreducible representation” should be supplemented by this argument.

The Hodge check is additional. On the norm-one circle, the two compact factors of Wρ₁⊗Wρ₂⊗Wρ₃ contribute z·z̄=1; on positive real scalars they contribute the extra |z|². At the remaining factor the same lifted Hodge circle acts as on V. Consequently U(1) and V⊗QK have the same full Hodge action under the intertwiner. This explicit cancellation excludes a residual CM character. It would fail for the same-sign choice (2,0),(2,0) on the compact factors.

The construction varies along the common upper half plane with fixed rational representation data. At the specified actual Mumford period, the derived group of Hg(B) maps onto Hg(U(1))=Hg(A). It is contained in G̃ and has the same dimension, hence is G̃ itself in its **faithful** action on W. This is compatible with Hg(A) being a central quotient; it does not identify the two faithful Hodge-group representations.

### 4.2 Repair P(6) by computing the center

The bridge's Galois-support argument is incomplete: a rational subspace of an isotypic component can be diagonal across equivalent summands. One must control its multiplicity-space characters.

The determinant over L maps the unitary Hodge group to

    T_L = ResF/Q U(1)_{L/F}.

The determinant of its Hodge circle has cocharacter proportional to (0,1,−1). The normal closure of F is totally real and is disjoint from imaginary K. The cubic Galois group permutes the three places transitively (C₃ or S₃); its orbit of (0,1,−1) spans exactly the plane with coordinate sum zero. Thus the connected determinant image is

    T₀ = ker(NL/K:T_L→U(1)_{K/Q})⁰,

of dimension two. Up to the finite intersection with G̃, the same torus is the connected scalar center of Hg(B); the determinant on this center is a square isogeny. This holds at every period satisfying the **actual** Mumford-group hypothesis, not just at a very general point: the determinant Hodge datum is fixed, and the derived-group assertion was just established.

The V-isotypic part of Λ³W_C consists of the eight choices of one standard summand at each σ_i. Its scalar characters are

    (t₁,t₂,t₃) ↦ t₁^{ε₁}t₂^{ε₂}t₃^{ε₃},    ε_i∈{±1}.

On t₁t₂t₃=1, a character here is trivial exactly when all ε_i are equal. Consequently precisely the two coherent summands can receive V, on which this center is trivial. No diagonal combination of nontrivial characters evades this test. The other representation types in Λ³W cannot receive V under G̃. On U(1), End_Hdg(V)=Q now gives

    Hom_Hdg(V,H³(B)(1)) = {v↦ψ(v⊗k):k∈K}.

This proves dimension two and the asserted image statement. It also proves primitivity: the nonprimitive summand of H³(B) is θ_B H¹(B), whose G̃-representations are single-factor standards, not V.

**Quantifier restriction:** this dimension statement does not extend automatically to CM fibers or arbitrary special fibers of a family called “Mumford-type.” Their actual Hodge group and End⁰(A) may differ. The construction and Weil theorem still make sense there, but redo the Hom computation if such fibers are included. Do not simultaneously define A by End⁰=Q and then assert P(6) uniformly at the excluded CM fibers.

## 5. R1 and R2: exact degrees and what remains conjectural

### 5.1 R1 survives, with twists

Antisymmetrization lifts a class ξ∈H^{2p}(Aⁿ,Q(p)) to tensors in V^{⊗2p}(p), allowing the factor labels and finite sums required for Aⁿ. Choose a nonzero embedding φ_k:V→U(1). The transported untwisted tensor belongs to

    U^{⊗2p} ⊂ H^{6p}(B^{2p},Q)

and has type **(3p,3p)**, not (p,p). Equivalently its twist (3p) is a Hodge class. Corpus Weil Theorem 1.1 makes it algebraic, and in particular transports the quartic target to codimension six on B⁴.

Since HC holds on B² as well, a Hodge projector onto U is algebraic as a cohomological correspondence: its tensor class is in H¹²(B²,Q(6)), using H⁹(B) dual to H³(B). One may speak of the homological-motive summand U(1), with Tate twists and algebraic Lefschetz operations specified. This is legitimate. **An abstract Hodge isomorphism of that summand with H¹(A) is not thereby an algebraic correspondence to A.** That is precisely the unproved link.

### 5.2 The one-class implication is valid

Take Γ∈CH²(A×B)_Q with nonzero component α in H¹(A)⊗H³(B). Algebraic Künneth projectors isolate α. Fix ample classes θ_A,θ_B. The identification with a Hodge morphism uses

    b_A(v,w)=∫A v w θ_A³ : V⊗V→Q(−1).

The **actual forward correspondence** is

    Γ_f = pr_A^*(θ_A³)·Γ ∈ CH⁵(A×B)_Q,

with the relevant projectors understood. Since dim A=4, it acts as

    H¹(A) → H³(B)(1).

A bare CH²(A×B) correspondence instead shifts degree by −4 and does not directly act this way. The bridge has to state the Lefschetz normalization, not just call Γ a map.

By §4.2 the induced φ is nonzero, lands in U(1), and is injective because V is simple. The primitive polarization of H³(B) uses θ_B³. Up to the fixed polarization sign, the reverse adjoint is represented by

    Γ_b = pr_B^*(θ_B³)·transpose(Γ) ∈ CH⁵(B×A)_Q.

It acts H³(B)→H¹(A)(−1). The composition has codimension 5+5−6=4 on A×A, as required for an endomorphism of H¹(A). Polarized Hodge theory gives

    φ♯φ = c·id_V,          c∈Q×.

Nonvanishing follows from nondegeneracy of the polarization on the sub-Hodge structure φ(V), not merely from abstract nonvanishing of φ. Its primitivity was proved above; alternatively one can use the algebraic Lefschetz-decomposition polarization on all of H³.

Transport the tensors for any ξ to B^{2p}, apply HC there, and apply (c⁻¹φ♯)^{⊗2p}. Algebraic correspondences and diagonal pullbacks recover ξ on Aⁿ. In each degree the forward tensors gain codimension 2p and the reverse operations remove it. Standard Künneth projectors and inverse Lefschetz correspondences on abelian varieties are algebraic; no extra standard-conjecture assumption is introduced.

Thus **any one nonzero rational class in this two-dimensional Hodge space suffices**. This is a conditional theorem, not an existence proof of its hypothesis, and not a demonstrated equivalence with HC on A's powers.

### 5.3 The GHC and Abel–Jacobi formulations need precise wording

The correct equivalence is

    some nonzero partner class is algebraic
      ⇔ U⊂N¹H³(B,Q)
      ⇔ the algebraic Abel–Jacobi image contains a positive-dimensional
         abelian subvariety with nonzero U-component (after projection).

For the first forward implication, restrict the first leg of Γ to a smooth complete-intersection curve C⊂A. H¹(A)→H¹(C) is injective, so the relevant class remains nonzero. A cycle of codimension two in C×B has total dimension five, and its image in the sixfold B is contained in a divisor. It therefore supplies a nonzero V-copy in N¹H³(B). The K-action generates all of U from that copy. More precisely, the action of a∈K on B induces **a³**, not a, on the coherent cubic tensor pieces. For u²=−d, u³=−du still generates K, so algebraic pullback by a cleared-denominator endomorphism supplies the needed second copy. This avoids silently assuming an algebraic realization of an arbitrary abstract K-linear operator on U.

Conversely, coniveau one gives a surjective Gysin map from a finite sum of H¹(D̃)(−1), where D̃ resolves divisors in B, onto U. Polarizability supplies a Hodge section of a nonzero V-copy. Hodge maps among weight-one structures are induced, up to isogeny, by homomorphisms of the corresponding Picard/Albanese varieties; equivalently the relevant class on A×D̃ is a divisor class by Lefschetz (1,1). Pushing that divisor correspondence to A×B yields a CH² cycle with the required nonzero component. Smooth resolutions and a finite sum of divisors suffice; no smoothness assumption on the original supporting divisor is needed.

For the last formulation, specify nonzero **rational H¹ map** or a positive-dimensional image in the U-isogeny factor. Literal “meets J(U) nontrivially” can mean a torsion intersection and is not equivalent to GHC. A projection to U can be made algebraic using HC on B² from R1. The complex torus attached to U is an abelian variety up to the usual rational-lattice choices, and

    J(U) ~ A² ~ A⊗Z O_K

is an **isogeny** statement, not a canonical integral isomorphism.

If A=J(C) for the specified genus-four curve, every Hodge map H¹(C)→H³(B)(1) lands in U by P(6), so a nonzero Abel–Jacobi homomorphism from this J(C) has the right component. For an arbitrary parameter curve this automatic conclusion is false: it may map to other level-one factors of H³(B). Require the U-component explicitly. Merely naming the BHPS curve and an abstractly constructed B also does not provide equations or an explicit cycle on B.

## 6. Stress tests: what the computations do and do not prove

### 6.1 Independently checked partner tangent rank

[check.py](../experiments/geo_partner_review_r3/check.py) is an independent exact implementation of the partner exterior tensor and symplectic tangent action; it imports no prior experiment. It uses rational arithmetic, a symplectically normalized basis and all 55 symmetric deformation directions in the polarized tenfold space. Its [output](../experiments/geo_partner_review_r3/check.out) gives rank 54 for coherent coefficients (1,1), (1,−1), (1,3), (2,5), and rank 38 when one coefficient is zero. It independently checks the augmentation-torus rank and coherent-character criterion for both C₃ and S₃.

The zero-coefficient tensors are complex single-eigenspace tests, **not nonzero rational partner classes**. A rational nonzero map has both conjugate coefficients nonzero. Over C, a symplectic scalar change on one pair Wρ_i,Wρ̄_i replaces coefficients (a,b) by (at,b/t), preserving the Hodge decomposition. Together with scaling the tensor this normalizes any ab≠0 to (1,1). Thus the nonzero-coefficient partner rank is not restricted to the numerical ratio 3. This validates the infinitesimal claim for the constructed rational partner class in the marked polarized ambient domain.

I read the Q_f experiment. Its isolated choice of three distinct coefficients establishes the rank for that model; a claim for **all** coefficients/periods needs either the stabilizer argument or a symbolic rank analysis. Do not use a finite sample as that missing proof. Likewise a finite cyclic-cover search only excludes its enumerated cover data; it does not exclude every geometric realization of B.

### 6.2 Local smoothness requires an extra argument; global reducedness does not follow

A tangent kernel of dimension one alone is not a proof that a global Hodge locus is a reduced curve. To conclude local smoothness, one must identify a genuine nonconstant analytic curve carrying the **same flat rational tensor** through the point. The compatible A/B construction in §§3–4 supplies such a curve for Φ locally. In a smooth marked ambient space, its presence gives local dimension at least one; tangent dimension one then makes the local analytic ring regular of dimension one. This is a **local-germ** argument. It does not classify other components, establish global irreducibility, or prove all Hodge loci reduced elsewhere. Delete the bridge's unqualified global sentence.

The deformation dimensions 36 and 55 refer to polarized abelian eightfolds and tenfolds, respectively, allowing deformations that lose the product decomposition. They are not the dimensions of Def(A)×Def(A) and Def(A)×Def(B), which are 20 and 31. State the ambient space when calling the locus rigid.

### 6.3 Spreading and semiregularity

CM density is insufficient. Relative Chow/Hilbert parameter spaces give countably many algebraic loci; countably many special points on a curve can all be isolated images of different components. **Adding one arbitrary non-CM point does not change this argument.** A very general point relative to a specified countable field of definition, a component known to dominate the base, or a suitable unobstructed deformation argument would be different hypotheses. Uncountably many algebraic fibers force a dominating component in the usual countable-parameter setup, after the standard base-change/spreading steps. They are a sufficient strategy, not a necessary condition for any possible proof.

Semiregularity must test the actual full obstruction theory: for a regular immersion the relevant obstruction subspace of H¹(N), and for a sheaf/perfect complex the appropriate Ext² obstruction space with the required trace/invariance conventions. The image of the **ambient** Kodaira–Spencer obstruction map is only one subspace. A rank-35 or rank-54 Hodge-variation calculation neither proves injectivity of the semiregularity map on the full obstruction space nor proves that every suitable seed must have the asserted obstruction dimension. Normalizing signs and knowing the cohomology class are not substitutes for calculating the seed's obstruction map. The bridge's numerical “absorb a rank-35/54 image injectively” discussion should be demoted to a possible necessary compatibility check under additional hypotheses.

The modest exclusion that uniform cycles in a full Sp-generic abelian family give Sp-invariant classes is valid. It does not rule out constructions whose auxiliary data or existence locus is already special to the curve. A short list of familiar Lefschetz constructions is not a no-go theorem for all geometric seeds. The admitted assertion about Albanese factors of Shimura surfaces remains a heuristic, not a proved exclusion.

### 6.4 Two further overclaims must be removed

**“Every linking class is rigid” is false with the stated scope.** The exact KS tensor on a fixed rank-9 quadratic space remains a Hodge tensor throughout its seven-dimensional K3 period domain, with the KS variety varying. The isogeny KS~A³² need not persist off the Mumford curve; that restriction explains why this does not solve the target, but it does not restore the blanket rigidity claim. H8 makes this distinction explicitly. The computations concerned Q_f and Φ, not every link to every possible auxiliary variety.

**“Each link is algebraic at CM points by the corpus CM theorem” is unjustified for KS.** At compatible CM periods, A and the PEL partner B are CM abelian varieties, so Φ and Q_f on their products are covered. A K3 surface is not a CM abelian variety. Algebraicity of its KS correspondence needs another theorem with the exact hypothesis. The rank-9 ambient K3 construction may acquire extra (1,1) classes there; its actual transcendental rank drops, and its full ambient Clifford tensor is not automatically covered merely by applying a theorem to the smaller transcendental space. Do not use this as an unproved semiregular seed.

### 6.5 The A² Weil route

The narrowly stated S(ii) survives: if End⁰(A)=Q, any unital K⊂End⁰(A²)=M₂(Q) acts on the multiplicity factor of V⊗Q². Sp(V) is K-linear with determinant one, so Λ⁸_K H¹(A²) consists of Lefschetz-group invariants. Its Weil plane supplies no exceptional quartic class by this construction. This does not follow from the withdrawal and does not reinstate the withdrawn eightfold theorem. It is a limitation of this A² route, not a new Hodge result.

## 7. R3: a valid known reduction, with an exact repair

The bridge's compressed step “Nikulin applies since 9+9<22” and its passage from a left inverse on the whole Clifford module to the prescribed p_f do not constitute the requested proof. The following argument repairs the conditional theorem. It also explains why its novelty was already exhausted in H8.

### 7.1 Quadratic space, K3 realization and KS multiplicity

Put T₀=Lie Hg(A) with its weight-zero adjoint Hodge structure and T=T₀(−1). Identify T₀ with the trace-zero quaternions D⁰. For totally positive λ∈F, use

    qλ(x,y)=TrF/Q(λ·trd(xy)).

At the split real place this has signature (2,1); at each Hamilton place it is negative definite. Thus T has rank 9, signature (2,7) and Hodge numbers (1,7,1). Literal T_S≅Lie(Hg A) without (−1) is a weight error. The choice is an F-scaled trace form, not an unspecified universal “rational scaling.”

There is a rational isometric embedding (T,qλ)↪Λ_Q, with Λ the K3 lattice. One precise justification is to prescribe the rank-13 complement's determinant, local Hasse invariants and real signature (1,12). Rank at least three allows the finite local data, and their product constraint follows from the global data of T and Λ. The quadratic-form local-global existence theorem then gives the complement and Hasse–Minkowski gives the embedding. This avoids invoking an unverified integral Nikulin criterion. Intersecting with Λ provides the required rational marking/lattice realization; no prescribed integral discriminant form is being imposed.

The given period line of T is positive and isotropic, so period surjectivity gives a K3 surface S. The adjoint representation has no rational Hodge-invariant vectors because the **actual** Hg(A) is the stated semisimple group. Hence T has no rational (1,1) classes, NS(S)_Q=T⊥ has rank 13 and signature (1,12), and S is projective with T_S=T. This proves the assertion at every allowed A period.

Over Qbar, T₀ is the orthogonal sum of three ternary adjoint representations. The product Spin₃³→Spin₉ has central kernel consisting of sign triples with product one. The spin representation of Spin₉, dimension 16, restricts as **two copies** of Std₂⊗Std₂⊗Std₂. The full even Clifford module C⁺(T), dimension 256, is sixteen copies of that spin module and hence **32 copies of V**. Absolute irreducibility of V gives the same decomposition over Q by the intertwiner argument. Its Hodge circle is the lift through the one noncompact factor; there is no continuous extra central circle in G_m·r(G̃). With weight one fixed, this is the same Hodge structure as V³². Therefore the full KS variety is isogenous to A³² and has dimension 128, as required. This checks both the representation dimension and the possible central-character issue.

### 7.2 Recover the desired algebraic projector through one block

Assume the exact j_w tensor is algebraic. Corpus K3 Theorem 1.1 makes every m_f∈End_Hdg(T)=F algebraic on S×S. After the isogeny KS~A³², take a **nonzero block**

    κ:T→H¹(A)⊗H¹(A) ⊂ H²(A²).

It is algebraic because it is obtained by algebraic inclusions/projections of the isogeny factors. Under the group action, the adjoint representation T₀ occurs with multiplicity one in End(V); its three geometric constituents are precisely the three S_i inside Sym²V. A nonzero rational block is injective: End_Hdg(T)=F is a field. Let κ♯ be its algebraic polarization adjoint and a=κ♯κ∈F×. Nonzero a follows from the polarized sub-Hodge structure. The algebraicity of all F-endomorphisms gives the explicit algebraic projector and its F-twists

    P_f = κ ∘ m_f ∘ m_{a⁻¹} ∘ κ♯.

After extension to a splitting field these are Σσ_i(f)p_i. This supplies the missing step: an arbitrary algebraic left inverse on the full KS module does not automatically identify these normalized projectors; a nonzero block plus its adjoint does.

Tate twists and cycle operations are legitimate here: κ is represented by CH²(S×A²), acting H²(S)→H²(A²); the reverse adjoint uses the polarization/Lefschetz normalization on the dimension-eight A², giving a degree-preserving correspondence in CH⁸(A²×S). Composition gives CH⁸(A²×A²). Passing to the multilinear quartic tensor uses algebraic inverse Lefschetz on the two H¹ source legs, and accounts for the ordinary Koszul signs. Now use the established quartic tensor-generation/all-powers reduction, already audited in R2 and present in H8; there is no need to present its finite closure again as new research.

This proves the conditional HC conclusion. Alternatively, H8's `thm:mumfordks` gives a direct Clifford-block proof of RM and the exceptional classes without this corpus shortcut, followed by `thm:mumfordpowers` and the stronger mixed-product corollary.

**Do not interpret the 4-dimensional closure experiment as “the exact KS tensor without an additional RM hypothesis can yield only four dimensions.”** It computes the closure after replacing the full tensor by the single total adjoint projector and thereby discarding information. The exact Clifford blocks themselves force additional F-data in the H8 argument; under the accepted corpus, the exact tensor already implies all m_f. The finite statement about a restricted list of generators can be retained, but that claimed mathematical necessity cannot.

## 8. Final disposition

P, with the cover/center/polarization/determinant repairs above, is a valid classical Hodge-theoretic construction whose split specialization reaches the accepted Weil-sixfold theorem. R1 is an unconditional consequence **about B**. R2 is a valid and precisely typed **conditional** reduction, with GHC equivalent to the missing partner-cycle hypothesis. R3 is an already public conditional theorem with a repairable proof; its advertised novelty and extra-RM interpretation fail. The stress tests support particular local infinitesimal statements, not a global obstruction theorem or an exhaustive list of ways a proof must proceed.

**No algebraic partner class, no rank-9 algebraic exact KS tensor, and no previously unresolved Mumford Hodge class has been produced. Consequently there is no genuinely new solved Hodge case to promote.** Keep the balanced-partner observation, if desired, as a corrected and attributed reduction with unverified literature novelty. Do not count it as substantive progress meeting the user's demand for a newly solved high-importance target.
