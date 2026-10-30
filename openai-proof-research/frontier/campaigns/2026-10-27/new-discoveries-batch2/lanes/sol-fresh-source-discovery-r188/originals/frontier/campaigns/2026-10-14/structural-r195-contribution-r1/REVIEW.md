# Structural195 — independent substantial-contribution review, round 1

**Verdict: TECHNICAL, conditional on correctness of the ENTIRE unchanged frozen theorem and its submitted proof.** This is a contribution assessment only. It issues no correctness verdict, acceptance, campaign count, repair, replacement theorem or downstream authorization. No finding from the other review role was read or inferred. The parent alone integrates and adopts dispositions.

The assessed statement is exactly `fresh-structural-discovery-r195/FROZEN.md`, 2265 bytes, SHA256 `823bddbdf60d3827d4f0cbf5684d559de760646b811f1626db497ed1786f8be8`. The submitted proof is `AUTHOR-PROOF.md`, 34147 bytes, SHA256 `c0c2a3205e9f5a1eccb5fb5dbc87c97402c1740c251fe4c0f40aa0cf86c7cc27`. All operative upstream proofs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. In particular the assessment pays for the source's single counterexample, not merely its algebraic setup. A conflict with a conjectural expectation is no reason to withhold that payment.

The relative family is a genuine strengthening of the printed single-object conclusion. Nevertheless, after paying for the actual construction and its usable proof hypotheses, its remaining operations are compatible elementary parameter and support extensions. The argument below accounts for the whole family, the relative quantifier, and every frozen consequence. The assessment does not rest on the headline, on inaccessible literature, or on a claim that support separation alone constructs spectra.

## 1. Exact scope and comparison baseline

Fix ANY prime p admitting an odd M with M≥81, p>16M², and 2 floor(M/8)>p^(1/3). Fix one such M for this p. These are the source operator hypotheses; they imply its geometry and triangulated-comparison hypotheses, including p>5 and p>8. Put β=log_p(2 floor(M/8)), so β>1/3. The choices below introduce no further inequality involving p and no intersection of infinitely many large-prime sets.

The generator b_p is precisely the p-completion of the source's standard regular BP-module quotient by the Araki v_i for i>2. Its comodule and Steenrod identifications are those of `comp:bp-comodule` and `comp:standard-cohomology`. It is not an unspecified form of BP⟨2⟩ and is not equipped here with an extra multiplicative structure. Thick means finite sums, all integer shifts, cofibers and retracts in p-complete spectra. Tensor-ideal closure is never added.

For this p the theorem supplies countably many connective p-complete X_j with finite p-group homotopy in EACH degree. Each is fp of EXACT fp-type two: finitely presented mod-p Steenrod cohomology, finite total homotopy after the type-three finite test, and failure of the corresponding type-two test. Each has BOTH canonical localization equivalences L₂ᶠX_j→L₂X_j and L_T(2)X_j→L_K(2)X_j. Each is outside Thick(b_p,X_i:i≠j), with all other positive indices allowed. The order embedding, continuum cardinality and nonfinite generation of C_N are part of this same assessment, not optional corollaries left unpaid.

The strongest baseline is Source319's complete single-object construction, including its nontrivial geometric action, completion and topology, moment operator, gluing lattice, microlocal ghost obstruction, triangulated comparison, reduction and central nilpotence, transfer, exact height and restricted telescope conclusions. All eleven canonical textual blobs were read in full. The twelve blobs were authenticated against the complete pinned tree, including the wrapper's ordered includes; the compiled PDF was authenticated only. No family-independence or nonuniqueness theorem in the actual introduction, comparison or consequences replaces the analysis below. The source's discussions of local tensor ideals and connective multiplicative obstructions have different scope.

In source notation k=F_(p²), R=k[[x]], Ω=k[[H]], Δ=R[[H]], Λ=μ_(p+1), and gr Ω=k[A,B,C], with weights 1,1,3. T′ is the reduced complete generator. E is the source's periodic invariant coefficient algebra. The exact completion functor realizes perfect E-modules and supplies their intrinsic topology. Write C_comp for objects with perfect completion and C_fin for those also having finite sections homotopy in every degree. These conditions are stable under the finite operations and retracts at issue. Nothing below requires an infinite sum to belong to C_fin.

## 2. The high-degree initial symbols are an elementary compatible input extension

### 2.1 Coefficient weight and tame lifts

The source's ordered-coordinate filtration continues to work when the weight 4 assigned to x is replaced by any W>3. The interchange estimates have strict gain: the first-coordinate commutator starts in weight 3>2; commutators with the third coordinate start at least in weight p>4; the coefficient commutator has weight at least 2W>W+3. Thus the same ordered monomials give gr_W Δ=k[X,A,B,C], with weights W,1,1,3, and the topology is unchanged. Normality and regularity of x are inherited from the skew construction. This reweighting is auxiliary bookkeeping, not a new analytic estimate or a modification of the resulting operator.

Over k the first-digit plane diagonalizes under Λ with reciprocal characters χ and χ^(-1). Since |Λ| is prime to p, the character projectors give exact eigenlifts V₁,V₂ in Ω with symbols A,B. The product V₁V₂ and the source's third-coordinate element U₃ are invariant. This is the usual finite tame averaging operation applied to the source action, not a new lift of the group action.

### 2.2 Irreducibles and the first-congruence condition

Choose strictly increasing prime integers d_j≥p. Over k there are (p^(2d_j)−p²)/d_j monic irreducibles of degree d_j; they have nonzero constant term. Choose one f_j and set

    P_j=(AB)^(3d_j) f_j(C²/(AB)³)
       = Σ_h c_(j,h) C^(2h)(AB)^(3(d_j−h)),     e_j=6d_j.

This is a polynomial of weighted degree e_j. It is tame invariant, fixed by simultaneous sign change of A,B,C, and not divisible by A, B or C. Over the algebraic closure it factors as the product, over the roots α of f_j, of C²−α A³B³. Each quadratic is irreducible over the rational function field in A,B because the A-adic valuation of α A³B³ is odd; Gauss's lemma gives polynomial irreducibility. Frobenius acts transitively on these factors, so a proper factor defined over k cannot be a union of Frobenius orbits. Hence P_j is irreducible over k. Distinct e_j make the P_j nonassociate.

Use the invariant lift

    b_j=Σ_h c_(j,h) U₃^(2h)(V₁V₂)^(3(d_j−h)).

The source's H₂=H(2) first-congruence quotient H/H₂ is the additive group of k, of order p² and exponent p. Its group algebra in characteristic p is commutative; every element of its augmentation ideal has p-th power zero. The image of U₃ is zero. Terms with h>0 therefore vanish in k[H/H₂]; the term with h=0 vanishes because the augmentation element V₁V₂ is raised to 3d_j≥p. Thus b_j has exactly the zero pushforward required for the source's initialization. This is the decisive compatibility: choosing irreducible symbols alone would not suffice. Here norm-like homogenization and augmentation nilpotence supply it explicitly at the already fixed p.

### 2.3 Why the source operator accepts these inputs without a new prime bound

In `op:initialization`, the special input U₃ is used for zero pushforward on H/H₂, tame invariance, and the identification of the eventual initial symbol. The first p² normalized orbit values form the source's Vandermonde system. Zero pushforward makes its initial moment errors divisible by x, so solving that system changes the measure by coefficients in xR. Tame averaging preserves the zero moments and the reduction. The factor h_g^(-1/2) used in the measure/operator correspondence is 1 modulo x and preserves that reduction as well.

After the first p² moments have been killed, the actual `op:coefficient-control` and `op:operator` proofs proceed by their orbit-index estimates, divided differences, digit matching and the fixed M inequalities. The controlling digit polynomial and M are not the degree of b_j in the group coordinates. Subsequent corrections remain x-divisible; their scale estimates and persistent unmatched digits are those already proved by the source. Therefore the construction accepts b_j and produces a_j≡b_j modulo x, finite crossings and a persistent-defect lower bound c_j N^β. Constants and starting scales may depend on j; the exponent β and the prime hypotheses do not.

Choose W>e_j. Every x-divisible correction then has weight greater than e_j, so σ_W(a_j)=P_j. This holds for the SAME a_j for every sufficiently large W. There is no need to construct a uniform finite W for all j and no need to change a previously constructed object when a new index is added. The author has made the source input more useful, but the construction remaining after these explicit checks is its original construction.

### 2.4 Gluing is paid at the level of maps and lattices

For m_j=cofib(a_j) and the source finite sum of periodic shifts Y_j, `glue:overlap`, `glue:pairs` and `glue:object` use finite crossings and persistent defects. They match at least c_j N^β polar/kernel pairs at scale N, with the required independence of kernel projections modulo x^(qN+1), and produce the closed discrete cocompact gluing lattice V_j. The fracture pullback U_j=Y_j×_(LY_j)V_j has perfect completion and finite sections homotopy degree by degree. Its membership in C_fin is thus paid by the source's actual lattice construction. Merely specifying a perfect local module would not have paid this global step; the operator extension above preserves the exact inputs that do.

## 3. Non-coordinate support detection: the same microlocal and growth argument

### 3.1 Rees localization and principal ideals

For fixed j invert the homogeneous symbols outside (P_j), using the W filtration. The proof of `obs:microlocal-flat` is the operative microlocalization input. It constructs the truncated Rees localizations: commutativity modulo the Rees parameter s makes iterated commutators vanish modulo sufficiently high powers of s, supplying the left and right Ore relations; the denominators reduce to regular elements; localization is exact on the successive s-layers. Surjective transition maps and good finite filtrations permit the inverse-limit passage, followed by the union needed to recover the microlocal ring. These arguments use multiplicativity and regularity of the denominator symbols, not the fact that the excluded irreducible was the coordinate C. The complement of the homogeneous prime (P_j) has the same properties.

In the resulting graded localization every nonzero homogeneous element is P_j^v times a homogeneous unit. This follows by factoring out its maximal P_j power in the polynomial UFD; the remaining homogeneous factor is inverted. The source's increasing-filtration division argument now makes every left ideal and every right ideal principal: take the least initial P_j valuation and successively remove leading terms using completeness. Thus its domain, Ore-division and one-sided module arguments apply to S_j. This is not a claim that S_j is commutative, nor that x commutes with a_j.

Here x is a unit, and any a with symbol outside (P_j) is a unit. The operator a_j remains a nonzero nonunit. The right cyclic module S_j/a_jS_j is nonzero torsion. The source's tame decomposition makes Δ[x^(-1)] finite free over its invariant coefficients, using the faithful character of the unit x; combined with the left and right flatness just described, it gives the required flat E→B_j=S_j[t,t^(-1)]. The exact functor Ψ_j on C_comp has Ψ_j(T′)=B_j and nonzero torsion homology on U_j. Tame invariants are taken before this extension; no action on a localization that has not been shown invariant is silently assumed.

This pays the support-separation apparatus. It is the actual source Rees proof plus elementary homogeneous prime division, not an invocation of an unread microlocalization headline. The inaccessible Asensio–Van den Bergh–Van Oystaeyen original is unnecessary to this comparison and gives no novelty credit.

### 3.2 The kernel estimate is regular-sequence Hilbert bookkeeping

The first part of `obs:growth` is unchanged: the orbit functions in the kernel span a full R-lattice; Weierstrass preparation bounds the relevant integral orbit polynomial degree by O(n); the normalized Newton basis is integral by the balanced orbit valuation estimate; choosing s with the source orbit count exceeding that degree gives T=p^s=O((1+n)^(1/3)). Bhargava's original p-ordering argument explains the Newton divisibility operation; the source already pays for its particular balanced orbit geometry and exponent.

The residue kernel injects into functions on H/Γ_s annihilating the appropriate left translates of the two reductions. The source's ordered coordinates identify the initial power relations as A^T,B^T,C^T. The change of degree-one basis causes no problem: T is a p-power, so Frobenius sends an invertible linear change to an invertible linear change on the T-th powers. Thus the remaining dimension is bounded by

    dim_k k[A,B,C]/(P_j,Q,A^T,B^T,C^T),

where Q is the second initial symbol and Q∉(P_j). Irreducibility makes P_j prime, hence P_j,Q a regular sequence (if Q is a nonzero constant the quotient is already zero). For g=deg Q>0 its Hilbert series is

    (1−z^e_j)(1−z^g) / ((1−z)²(1−z³)).

There is a particularly direct bound here because e_j is divisible by 3:

    H(z)=(1+z³+...+z^(e_j−3))(1+z+...+z^(g−1))/(1−z).

Every coefficient is at most e_j g/3. After imposing the T-th powers, monomials have weight at most 5(T−1). Their total dimension is therefore at most (5T−4)e_j g/3, in particular O_j,Q(T). The estimate retains exactly the exponent 1/3. Its constants may grow with the symbol degree, but the later comparison with c_j N^β is for fixed j and fixed map, so this growth is harmless. No uniform-in-j estimate is being claimed.

The new non-coordinate count is thus a standard regular-sequence count replacing the source's coordinate monomial count at the LAST step of the same argument. It does not improve the orbit estimate, produce a new exponent, or impose an additional prime condition.

### 3.3 Correct-sided remainders and the adjoint

Two source reductions are needed to use this count. For a right x-saturated annihilator J containing a_jΔ and becoming the whole ring after microlocalization, right division and successive removal of the initial multiples of P_j yield an element with symbol outside (P_j). Otherwise completeness would keep J inside the nonunit ideal generated by a_j, contradicting JS_j=S_j. On the left, a coefficient b′ not in S_j a_j is treated by clearing x denominators on the left, removing left multiples of a_j and dividing by x on that same side. An endless removal would converge into Δa_j, again contradicting the assumed nonmembership. These are the source's principal-initial-ideal remainder arguments; the linearity of C is not used once division and completeness are available.

The constant-term adjoint of cδ_g is

    g^(-1)(c) · x(g^(-1)x)'/(g^(-1)x) · δ_(g^(-1)).

Modulo x it is group inversion and on gr Ω it sends A,B,C to −A,−B,−C. P_j is fixed by this sign involution, so the adjoint preserves its prime ideal and the complement needed for the second symbol. The joint-kernel bound therefore applies to the adjoint operators with the same exponent. These side and involution compatibilities are essential, but their verification is direct algebra on the displayed symbols and the already paid source reductions.

## 4. Enlarging the dual-ghost targets does not add a new ghost theorem

The source states `obs:dual-ghost` for targets in Thick(T′). Its proof has more usable scope than that statement: the target enters through perfect completion and finite sections homotopy, not through a chosen finite expression in T′. `complete:topology` provides the continuous completion maps and the open/discrete-cocompact behavior for these intrinsic hypotheses; `glue:global-maps` is fracture naturality. This is why C_fin, rather than merely C_comp, is the correct enlarged class.

Here is the full mechanism retained for an arbitrary P in C_fin and a map g:U_j→P whose image under Ψ_j is an ordinary ghost. With the source's right-module convention, flatness on the left turns homology annihilation into a right annihilator J_h containing a_jΔ and satisfying J_hS_j=S_j. Section 3.3 extracts b outside the prime. Passing to the Laurent coefficient realization and the tame projection gives the source's projected annihilation identities. The projection is E-linear; it is not asserted to be Δ[x^(-1)]-linear.

The topology of P gives a compact open lattice and continuous constant-term functionals with a bounded x^(-L)R target lattice. The adjoint kernel bound makes the polar images have rank O(N^(1/3)). Discreteness of the global image makes its intersection with a compact set finite. Against the at least c_jN^β glued pairs, this leaves a killed span of dimension at least c_jN^β−O(N^(1/3)). Independence of the kernel projections is the source's independence, not a dimension guess about arbitrary kernels.

To test dual vanishing, precompose a completion functional θ into a free shift. The composite on a cofiber m_j[r] kills its inclusion, since a_j is nonzero in the domain coefficient algebra. It therefore factors as b′∂_r with the source's left coefficient convention after periodic normalization. If b′∉S_j a_j, the left remainder argument gives a second symbol outside the prime. The joint-kernel estimate would bound the same independent killed span by O(N^(1/3)), contradicting β>1/3 for large N. Thus b′∈S_j a_j and the factored map is zero after extension. The argument works for each free shift and each r.

For a perfect completed E-module M, perfect evaluation gives

    B_j ⊗_E RHom_E(M,E) ≅ RHom_(B_j)(M⊗_E B_j,B_j).

Right flatness lets this identification pass to homology. This proves the ordinary-ghost⇒dual-ghost implication at the enlarged target class used by the author, in the conditional contribution comparison. Every target property just used holds for C_fin. No step needs P itself to have a finite T′-tower. The extension is therefore an abstraction of the actual proof hypotheses, not an independent theorem about arbitrary targets or arbitrary complete modules.

Christensen's corrected original supplies the relevant classical finite-extension/projective-class framework. Theorem 3.5 identifies products of projective classes and powers of their ideals using actual triangles and retracts; Section 8 derives the ghost consequences using resolutions. The source then supplies the stronger particular two-test criterion required here. This review does not replace that criterion by a vague assertion that sufficiently many ghosts vanish.

## 5. Finite relative support separation and all other family members

The degree-two Galois involution τ acts semilinearly on the reduced categories, preserves T′ and the completion/finite-sections conditions, and intertwines the source pullbacks. The group coordinates and congruence filtration are defined over F_p. The first-digit plane and the leading third-coordinate line are preserved: terms from deeper first coordinates have weight at least p>3. Consequently τ preserves the weighted filtration and sends P_i to a homogeneous irreducible of the same degree e_i. It need not fix P_i. Distinct degrees are enough to separate P_j from BOTH P_i and τP_i for i≠j.

Fix j and a finite F⊂N\{j}. Take W larger than e_j and every e_i in F. This changes the common auxiliary detector, not the previously constructed operators. Since σ_W(a_i) and σ_W(τa_i) lie outside (P_j), these operators become units in S_j. Their perfect cofibers become zero; hence Ψ_j kills U_i and τU_i. On

    T_F=T′ ⊕ ⊕_(i∈F)(U_i⊕τU_i)

it takes the value B_j. Moreover T_F and every finite tower and retract built from it remain in C_fin, so Section 4 applies to every target in Thick(T_F).

Apply the source's `rew:obs:tower-criterion` with this T_F. Its complete induction is relevant: every finite thick construction is a retract of a finite tower with layers finite sums of shifts of T_F, by octahedra and retract closure. Over the two-sided principal domain, the periodic perfect image splits into free shifts and torsion homology with length-one resolutions. Starting from the zero tail and going backwards, dual vanishing eliminates the free projection as an actual derived map. The residual ordinary homology map factors from torsion into free modules and is zero. The two-test implication restores dual vanishing for the preceding tail. A retract insertion of U_j into such a tower would therefore act trivially on its nonzero torsion homology, an impossibility. Thus

    U_j ∉ Thick(T′,U_i,τU_i:i∈F).

This is precisely ordinary finite support separation implemented through the source's global-to-microlocal two-test mechanism. The nonzero torsion at j and units at every other degree are the elementary support calculation; the difficult lifting to an ordinary global thick obstruction is already paid by the source's criterion and the intrinsic-target observation above.

Countability requires two separate elementary arguments. First, at the single fixed p there are infinitely many d_j and hence the constructions of Sections 2–4 for all j, with no j-dependent prime hypothesis. Second, a finite expression witnessing membership in a thick closure uses only finitely many generators, even if the generating collection is infinite. Therefore a hypothetical membership against ALL i≠j would already occur for some finite F. Neither argument assumes a countable coproduct or a uniform W for the entire family.

## 6. Relative transfer retains the conjugates and both nilpotent boundaries

It remains essential to compare the family in spectra, not just in the reduced category. Set F_i=e_*r^*U_i in the source notation, and let Z_i realize i_*F_i under the homology-compatible triangulated comparison. Set X_i=τ_(≥0)Z_i. The source transfer criterion applies to each U_i by the empty-F case above, finite sections and perfect completion. It supplies the degreewise finite p-groups, p-completeness, L₂X_i=Z_i and nonmembership against b_p. Its actual integral and central constructions are already part of the baseline.

Suppose now that X_j belongs to Thick(b_p,X_i:i∈F), where j∉F and F is finite. Exact L₂ and the source comparison give

    i_*F_j ∈ Thick(T_(Z_p), i_*F_i:i∈F).

Apply the exact derived reduction Li^* and put R_i=Li^*i_*F_i. The standard generator identification gives

    R_j ∈ Thick(T₀,R_i:i∈F).

The reduction triangle is the actual triangle F_i[1]→R_i→F_i→F_i[2]. In particular R_i∈Thick(F_i). Conversely, the source's uniform-on-all-shifts nilpotence of the reduction boundary on F_j, with its exact-functor cone hypothesis, gives F_j∈Thick(R_j). This implication uses octahedral assembly of the cones of iterates; the cone of a zero iterate contains the object as a retract. It does not assume that the boundary transformation commutes with suspension. `transfer:central-completion` establishes this nilpotence for arbitrary perfect-completion inputs by sparsity (D>12), the pure open and the actual fracture square. It does not require U_j∈Thick(T′).

Extend to k. Ordinary separable degree-two descent gives

    e^*e_*G ≅ G⊕τG.

This is the explicit factorization k⊗_(F_p)k≅k×k with its two embeddings, compatible with the source groupoid maps and twists. Hence r^*U_j is a retract of e^*F_j. Keeping the other terms, rather than dropping them, yields a finite expression for r^*U_j from T_k and e^*R_i. Since R_i∈Thick(F_i), each e^*R_i lies in Thick(r^*U_i,r^*τU_i).

Apply the exact Q=Rr_* with Q(T_k)=T′. The actual central triangle

    V → Qr^*V → V[−1] → V[1]

gives Qr^*V∈Thick(V). For V=U_j its boundary ε is nilpotent uniformly as supplied by the source's complete/open/fracture argument. The same finite cone argument gives the converse containment U_j∈Thick(Qr^*U_j). Combining all these containments gives

    U_j ∈ Thick(T′,U_i,τU_i:i∈F),

contradicting Section 5. The two nilpotent triangles were used in their actual directions; neither was split. The Galois conjugates were retained until the support detector killed them. No tensor-triangulated enhancement was needed.

This is a relative use of the source's exact functors and nilpotence lemmas. The extra bookkeeping matters, but no new descent object, new nilpotence estimate or new all-degree comparison is required. The source statements already have the arbitrary-input scope used here. Distinct-degree separation handles the only extra summands produced by the classical finite-field descent. This closes the proposed relative residual without weakening its quantifier.

## 7. Every spectral assertion and consequence is paid objectwise or formally

For each j, the source transfer construction produces the connective p-complete X_j with finite p-group homotopy in every degree. If V is a finite type-three p-local spectrum, E(2)-locality and finite duality give V∧Z_j=0. The triangle from X_j to Z_j identifies V∧X_j with a shift of V smashed with the negative tail. The left description is bounded below and the right one bounded above; each group is finite. Thus the total homotopy is finite. Mahowald–Rezk Proposition 3.2 identifies this finite-total property with fp-ness in the required setting and gives fp-type at most two. Proposition 3.5's connective-local construction and Section 7.2's localization discussion are consistent stronger antecedents, not new claims credited to this family.

Type at most one is excluded by the actual Lee–Pstragowski height-one theorem, with the source's finite-homotopy hypotheses. Its proof makes connective covers in the height-one local thick category lie in the thick category generated by completed BP⟨1⟩, retaining the finite Postnikov corrections. The source's `scope:exact-height` identifies this standard generator as the completed v₂-cofiber of the specified b_p, hence in Thick(b_p). A lower type would put X_j in Thick(b_p), contradicting even the empty-family case. This retains EXACT type two, not only an upper bound.

The negative tail N_j=τ_(<0)Z_j has finite p-group homotopy in each degree. Its finite Postnikov ranges are built from HF_p and it is obtained by the source's directed tail construction. HF_p is acyclic for L₂ᶠ and for T(2) and K(2), so those functors kill N_j. E(2)-local Z_j is L₂ᶠ-local. Consequently the canonical L₂ᶠX_j→L₂X_j identifies both sides with Z_j. For the height-two comparison, the source's restricted E(2)-local argument applies to Z_j: the fiber of its K(2) comparison, after T(2) localization, has vanishing K(0), K(1) and K(2); it is still E(2)-local and hence zero. Smashing T(2) localization and E(2)-locality supply the compatibility in that argument. Removing N_j gives the canonical L_T(2)X_j→L_K(2)X_j equivalence. This uses the source's full `scope:telescopes`, not an unrestricted telescope conjecture.

The same p and M work for every j. Constants for lattices, growth and nilpotence may depend on the individual objects and finite diagrams. None is asserted uniform across the countable sequence. The source's operator range implies applicability at every sufficiently large prime; this review introduces no numerical threshold.

For I⊂J, ordinary thick closure immediately gives C_I⊂C_J. Conversely if C_I⊂C_J and j∈I\J, then X_j∈C_J⊂Thick(b_p,X_i:i≠j), contradicting the full relative assertion. Thus I↦C_I is an order embedding of P(N), and its image has continuum cardinality. Each object of each C_I is formed by finitely many finite operations on bounded-below p-complete fp-type≤2 generators; bounded-below and the finite-total type-three property are stable under these operations and retracts. Hence every C_I has the frozen ambient restriction.

If finitely many Y₁,…,Y_m in C_N generated C_N, each Y_l would use only finitely many of the X_i. Let F be the union of those finite supports. Then Thick(Y₁,…,Y_m)⊂Thick(b_p,X_i:i∈F). An index j outside F contradicts the relative nonmembership. This is nonfinite generation of C_N by its own objects. It says nothing about finite generation of the entire fp category.

All exclusions remain in force: no explicit prime threshold, small-prime or other-height assertion, other-form extension, classification of all thick subcategories, whole-fp-category finite-generation statement, tensor-ideal statement, or further telescope/Picard/duality/K-theory consequence.

## 8. Strongest actual primary and original-history comparison

Lee–Pstragowski's final Springer text was read through all mathematical sections, including the operation algebra, local classification proof and height-one theorem. Theorem 4.3's equivalences concern local fp objects, finite Morava-operation cohomology, Thick(E) and reflexivity. The proof constructs appropriate Moore powers and a sufficiently small subgroup, uses the exterior-operation calculation and polynomial Ext/noetherian spectral sequences, complete filtrations and derived Nakayama, then finite resolutions and Galois descent. This is more than its title or abstract. Section 5's connective-cover argument is the actual input used above. Conjecture 1.1 and Note 1 give the recorded Hahn–Wilson attribution; neither supplies a global independent family or makes its failure automatically substantial.

Mahowald–Rezk's original Proposition 3.2 proof and Proposition 3.5, and its Section 7.2, were read. They pay for the finite-total fp criterion, connective-local examples and the relevant localization perspective. The unrelated Brown–Comenetz duality development is not used as a new conclusion here. Christensen's corrected text was read for the complete projective-class product argument and derived ghost section; the source's specialized two-test induction is still paid separately.

Pstragowski v2 Section 6 and Appendix B were read, including their proof qualifications and the triangulated comparison. Barkan v2 was read through the complete mathematical text, pages 1–27, beyond the author's stated partial read. Its stronger comparison uses the filtered Goerss–Hopkins deformation, square-zero τ-adic tower, obstruction groups for objects and multimaps, arity bounds, and sparsity degeneracy. Proposition 2.36, the complete proofs in Section 3 and the final chromatic specialization give the tensor-triangulated statement. It pays an even stronger available transport operation at the relevant large primes, but it does not supply the global gluing lattice or the relative support obstruction. The submitted proof needs only the source's stipulated homology-compatible triangulated comparison, so no monoidal novelty is credited. This is a comparison of actual proof operations, not an inference from Barkan's abstract.

Bhargava's actual Monthly original reprint, all pages 783–799, was read, including the p-ordering/Newton divisibility proof and integer-valued basis statements. The source's integral interpolation is an instance of that classical divisibility operation with its own already-paid orbit data. The rejected course PDF was not used. Hahn–Wilson v5 pages 1–8 were read for its actual statements and form limitations: its E₃-BP-algebra redshift assertions do not identify arbitrary Araki quotient forms with the required multiplicative forms. The redshift proof is not an operative antecedent of any frozen assertion and was not read or used. Its absence contributes nothing to the grade. Likewise the inaccessible 1989 microlocalization original supplies no favorable inference: the complete source proof already covers the operation assessed here.

Original project history was read from authenticated exact heading-bounded sections, not summaries: i105 [664,8740); i107 [927,3819), [13497,15450), [31276,34401), [34401,37109); and the four r39 `308-positive-transfer` sections comprising [953,7763). i105 distinguishes ordinary finite assembly from local tensor-ideal support and records Hahn–Wilson only as a neighboring lead. i107's stronger-companion and signed-fracture derivation illustrates paying the actual unframed comparison and maps; it is a different height-three rational-tail target. The r39 original explicitly carries finite diagrams, bases, relations and all-degree descent through a regular-sequence construction, distinguishing a technical compatible transfer from a mere homology-level claim. None is an earlier proof of this family. None is reopened or regraded. Their relevance is operation-level comparison and preservation of older scopes, not an inherited disposition determining this verdict.

A prospective authored-history lexical scan, with all requested exclusions already installed, found 1665 eligible UTF-8 files and 35 literal-term hit paths. It was navigation, not a proof search certificate. Additional heading-only disambiguation separated complete-intersection Betti, nonconical deformation and close-operator-algebra leads from this target. Only the exact original passages just listed are used as mathematical history evidence. The protected reading record gives the exclusions, coarse omissions, false admissions and exact semantic extents. No completed r194 body was admitted in this review.

## 9. Contribution decision and remaining obligations

The four proposed residuals have been tested against the strongest compatible operations, jointly:

| Proposed residual | Actual remaining operation after source payment | Contribution assessment |
|---|---|---|
| High-degree invariant irreducibles, first-congruence zero, survival of operator corrections | Finite-field irreducibles, invariant homogenization, augmentation p-nilpotence, tame averaging and an auxiliary coefficient reweighting; the source moment/digit construction uses precisely those retained properties | Explicit and useful, but a routine input extension of the paid operator |
| Non-coordinate microlocal kernel estimate | The same regular-symbol Rees/Ore proof, principal initial-ideal division, and a regular-sequence Hilbert series with bounded coefficients | Same exponent and orbit argument; classical bookkeeping closes the change of prime |
| Ghost implication for C_fin | Identify the two target properties already used in the complete source proof and keep its topological, sided and duality steps | A proof-hypothesis abstraction, not a new ghost principle |
| Relative transfer with conjugates and nilpotent boundaries | Retain every exact-functor image, use k⊗k=k×k, and apply both source nilpotence cone lemmas; distinct degrees kill the added conjugates | A finite relative composition of paid functors, with no new descent or uniformity theorem |

These operations fit simultaneously: the first-congruence condition enables the operator without a degree-dependent prime bound; reweighting protects the symbols without changing the operators; the regular-sequence count preserves the exponent beaten by β; the enlarged target condition is closed under the finite relative towers; and degree separation survives the Galois summands created by descent. These compatibilities are why the full conclusion, rather than only a one-object or finite-family weakening, is accounted for.

**No closed nonroutine residual remains after this integrated payment.** The countable family is a routine parameter extension of the source's one-object construction together with its available relative support and exact-transfer operations. That phrase does not mean that the printed single-object theorem logically implies the family without examining its proof, nor that the global source construction was easy. It means that the new work remaining after the stipulated construction and classical operations is the explicit compatible extension detailed above. The order-embedding, continuum and nonfinite-generation statements are then formal finite-support consequences.

There is no unresolved essential contribution-comparison step in this assessment. Literature access and reading limits are stated separately and are not treated as evidence of originality. No worldwide-priority or exhaustive-clearance claim is made. The theorem may be new as a project statement while still receiving TECHNICAL under the supplied acceptance criterion.

The condition on ENTIRE-THEOREM CORRECTNESS remains outside this role and undischarged by this review. All conclusions here are conditional on it; no claim of PASS or independent correctness follows from the derivational comparison or the artifact controls. The submitted scope and proof remain immutable.
