# Family319: arbitrary finite generators — no nominee

This is a pre-freeze mathematical screen, not a proved theorem or an independently reviewed contribution. Count remains 13/20. Source truths at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated throughout. No upstream theorem is challenged.

The natural question considered was whether, for every sufficiently large prime p, the category F₂(p) of bounded-below p-complete spectra of fp-type at most two has no finite ordinary thick generating set. Explicitly: for every finite list P₁,…,Pᵣ in F₂(p), does there exist a connective spectrum X of exact fp-type two outside Thick(P₁,…,Pᵣ)? Ordinary thick closure means finite sums, all integer shifts, cofibers and retracts, with no arbitrary tensoring or infinite constructions.

The two formulations are equivalent using the established height-one theorem. To pass from nongeneration to the exact-type-two version, first augment the proposed list by BP<1>. An object escaping this augmented list cannot have fp-type at most one. Shift the bounded-below escaping object to make it connective; thick membership is shift-invariant. Conversely, exact-type-two escape excludes a finite generator. Finite lists reduce to their finite direct sum. These observations are technical and are not a nomination.

This full question was announced provisionally before development. It was never frozen as a candidate theorem: the mechanism check below failed before a credible complete route emerged. No weaker conclusion is substituted.

## What the pinned source actually supplies

The source *Counterexamples to the Hahn–Wilson conjecture at height two* constructs, at every sufficiently large prime, a connective p-complete exact-type-two X outside Thick(BP<2>), for the specified standard regular quotient. It also proves telescope comparisons for that X. These conclusions, their local classification, and the failure of the naive connective-cover lift are already paid.

Its algebraic object lives in a twisted periodic derived category D(N). Write T′ for the chosen chart generator, completion as a hat, and L for inversion of the height-one section. A complete operation a gives

    m = cofib(a : T′hat → T′hat),   Y = ⊕(0≤r<D) m[r].

The overlap has kernel/cokernel defect spaces K and Q. A discrete cocompact lattice Λ in Q⊕K determines an open object V and a pullback

    UΛ = Y ×_(LY) V.

Source labels `glue:pairs`, `glue:object`, and `complete:topology` prove degreewise finite sections homotopy, UΛhat ≃ Y, and an intrinsic locally compact overlap topology. Its special paired lattice supplies at least cN^β defect pairs, β>1/3. For the target class used in the source, global maps preserve discrete lattice images.

The operation ring Δ has associated graded k[σx,A,B,C], with degrees 4,1,1,3. The source microlocalizes at (C), obtaining a two-sided principal domain S and B=S[t±1]. Completion and coefficient extension define an exact functor Ψ on objects with completion in Thick(T′hat). It sends T′ to B, while HᵢΨ(UΛ) ≅ S/aS in every degree; this module is nonzero torsion. The ring, functor and filtration are not changed by choosing another lattice for fixed a.

The source finite-tower criterion (`rew:obs:tower-criterion`) assumes Ψ(T₀)≃B. It also assumes, for every global map g:U₀→P with P in Thick(T₀),

    HΨ(g)=0  ⇒  H((Ψ(g))* )=0,

where * is derived module duality. The source proves this implication by integral annihilator extraction, a joint-kernel O(N^(1/3)) bound, and the larger paired-lattice exponent. In the tower induction, each cell is a sum of **free** shifts. A torsion-to-free homology map is zero; the dual test removes the free part of a tail as an actual derived map. Freeness enters both the cellular identification and the torsion-to-free step. It is not a generic perfectness assumption.

## A precise obstruction to deleting the free-generator hypothesis

Let k be a field, S=k[c]_(c), D=4, B=S[t±1] with t of cohomological degree 4 and zero differential. Let C be the full subcategory of Perf(B) with torsion homology over S, let Ψ be inclusion, and set T=U=B/cB. Then C is idempotent-complete and thick, U has nonzero torsion homology, and U belongs to Thick(T). Nevertheless, for **every** P in Thick(T) and every map g:U→P, H(g)=0 implies H(g*)=0.

Here is a proof of the last assertion. Every finitely generated torsion S-module is a finite sum of S/(cᵃ), a≥1. Each has a length-one free resolution. The periodic splitting argument over the hereditary ring S decomposes every perfect periodic object with torsion homology into the four periodizations of its shifted homology modules. Thus it suffices to examine a matrix component between shifts of two torsion modules M,N. Derived maps have only Hom and Ext¹ components; higher Ext groups vanish. A component visible on homology is precisely a Hom component between matching residues. Therefore a homology ghost has only Ext¹ components.

For a torsion module M, RHom_S(M,S) has its only cohomology in degree one, equal to M^∨=Ext¹_S(M,S); Hom_S(M,S)=0. Duality sends a map M→N[1] representing Ext¹ to a map N^∨→M^∨[1], up to a common shift. This is again an Ext¹ component and hence is zero on homology. Applying this to each matrix entry proves the implication, including arbitrary shifts, finite sums and retracts. All assumptions of the tempting replacement criterion hold except Ψ(T)≃B, and its proposed conclusion U∉Thick(T) is false.

This is an algebraic counterexample to a proposed inference. It is not a counterexample to the pinned theorem, to the full F₂(p) question, or an fp-spectrum construction. It remains valid even though U is itself a very short perfect object. It is not nominated as a result.

## Why the available variations do not yet repair this

1. **Changing only the lattice.** Every UΛ above has the same completion Y and the same Ψ-image. The legitimate algebraic object T′⊕UΛ₀ has finite homotopy in every degree and perfect completion, but its Ψ-image has both free and nonzero torsion homology. Replacing T′ by this object does not meet the source criterion. No claim is made that its ordinary thick closure contains all other UΛ; that is exactly the additional global problem.

2. **Changing the microlocal prime while retaining a.** The initialization and allowed later corrections satisfy a mod x=U₃ and σ(a)=C (`op:initialization`). At any analogous filtered localization where C is inverted, a is a unit: lift the graded inverse and correct errors in the complete filtration. Its cone, and therefore the proposed detector of UΛ, vanishes. At (C), the cone survives but arbitrary generators can carry torsion there. The source's later coefficient freedom preserves this initial symbol. The screen found no source operation that simultaneously moves the defect support, preserves the two quantitative kernel estimates, and avoids arbitrary prescribed generator torsion. This is a limitation of this route, not a classification of all possible operators or localizations.

3. **Extending the global ghost implication.** The topology proposition is already stated for all degreewise-finite objects; perfect completion supplies the module calculations. This suggests that portions of `obs:dual-ghost` may extend beyond Thick(T′). Even granting the entire implication for every proposed new target, the DVR example shows it is insufficient without a new replacement for the free-cell induction. Merely enlarging the target quantifier in that technical lemma is not the required result.

4. **A diagonal lattice.** A credible proof would need a statement forcing all maps from a newly glued object into arbitrary finite constructions from the prescribed Pᵢ to satisfy an obstruction that still detects a retract insertion. The existing estimate bounds polar rank only after a microlocal homology-vanishing assumption. It does not bound arbitrary maps into Pᵢ, nor does it supply a separation theorem for their gluing lattices. Countability of coefficient polynomials cannot enumerate all complete operations: formal power series over a finite field already form an uncountable set. Conversely, uncountability alone proves no nongeneration theorem, since mapping spaces and finite constructions may also have uncountably many choices.

5. **Transfer of arbitrary generators.** The source transfer criterion reverses reduction and central pullback using nilpotent comparison boundaries and the identities of the specific BP chart generators. A general Pᵢ must first be transported through the algebraicity equivalence and coefficient changes; the reverse thick-membership argument must target those actual images. One cannot simply replace the final symbol BP<2> by Pᵢ in `transfer:criterion`. The source source-object fp realization is useful, but does not establish the arbitrary-generator exclusion.

## Primary and companion comparison

Lee–Pstrągowski, *The monochromatic Hahn–Wilson conjecture*, arXiv:2410.08029v3, Section4, constructs local finite resolutions using the noetherian operation ring, then lowers projective dimension and descends after passage to a sufficiently small open stabilizer subgroup. Section5 lifts at height one using degreewise finite generation and connective covers. These are actual local finite-construction operations; they do not provide arbitrary global lattice separation. At height two, the pinned source explicitly shows that τ≥0E₂ fails even the necessary degreewise finiteness of mod-p homotopy for Thick(BP<2>), so the height-one connective-cover step cannot be silently reused. Primary source: https://arxiv.org/html/2410.08029v3 .

The pinned companion *Stabilizer orbits and thick tensor ideals of dualizable K(n)-local spectra* classifies invariant supports and local **tensor ideals** of dualizable objects. The natural question here concerns global fp objects and ordinary thick closure. Neither dualizability nor closure under arbitrary tensor factors has been established for that proposed category. Its classification cannot be applied merely because both questions mention thick subcategories.

The existing I105 report develops a different height-three rational-attachment problem and treats the Hahn–Wilson title as a comparison lead. The present source-operation screen therefore is not a renamed I105 proof. No worldwide priority claim follows from this history check.

## Disposition

The all-finite-generators question remains unproved and unrefuted. No target was frozen, no candidate is submitted, and no restricted BP-only or prescribed-torsion-free-generator result is offered in its place. The precise unpaid operation is an arbitrary-generator global separation mechanism, together with the compatible transfer of those generators. Fixed-completion lattice changes plus the existing two homology tests do not supply it. Reading limits and identity receipts are separate; neither hashes nor the algebraic diagnostic certify this proposed topological statement.
