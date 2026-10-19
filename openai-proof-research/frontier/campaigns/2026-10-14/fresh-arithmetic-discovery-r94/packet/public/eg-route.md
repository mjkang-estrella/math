# Source249 Eilenberg–Ganea routes: checked limitations, no target

Status: PREFREEZE. Nothing in this note is frozen, nominated, or offered as a contribution. The statements proved below are limits on methods. They are recorded so the routes are not reopened under another name.

Source249 is `preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026`, pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its `thm:main` gives a finitely generated, residually finite height kernel G = ker(λ: A_L → Z) with cd G = 2 and gd G = 3. Here L is a flag triangulation of the presentation complex of ⟨x,y | x²=y⁵, x²=(xy⁻¹)³⟩. The proof combines two parts. `thm:presentation` shows that if gd = 2, every sufficiently small labeling that is flat on the triangle words has trivial holonomy on every closed path. `prop:small-labels` builds small flat SU(2) labels on the level complex X that have nontrivial holonomy. The introduction says G is not finitely presented.

## 1. The Coxeter comparison runs the other way

Leary–Petrosyan, arXiv:2605.07853v1, §5.6, Corollary 5.21 (read in its actual body, together with Corollary 1.4 and Corollary 5.14), shows the following. If L is a flag triangulation of a Poincaré homology sphere spine and [W_L,W_L] is an Eilenberg–Ganea counterexample, then so is B_L. Its proof embeds [W_L,W_L] ≤ [A_L,A_L] ≤ B_L and uses cd [W_L,W_L] = cd B_L = 2.

So a Coxeter counterexample would give a Bestvina–Brady counterexample. The converse does not follow: a subgroup of a group with gd 3 can still have gd 2. Source249's result about B_L therefore says nothing about [W_L,W_L]. Leary–Petrosyan also note that a Coxeter counterexample would be a counterexample to Wall's D(2) problem, since [W_L,W_L] is finitely presented. That would be a famous central construction, not a closable compatibility.

## 2. Proved limitation: small transport is rigid for finitely presented groups

The prior runner observed that a fixed finite acyclic chamber has an isolated trivial SU(2) representation. I re-derived that observation and generalized it. The general form explains why source249's mechanism needs a group that is not finitely presented.

**Proposition L1.** Let Γ be a finitely presented group. Let Γ act freely, cellularly and cocompactly on a connected CW complex X with H₁(X;Z)=0. Let U be a compact subgroup of some U(n), with the operator-norm distance |a−b|. (SU(2) as unit quaternions with the quaternion norm is the case used in source249.) Then there is η>0 with the following property. Suppose an edge labeling h_e ∈ U satisfies h_ē = h_e⁻¹ and |h_e−1|<η for every oriented edge, and the product around the boundary of every 2-cell is 1. Then the product around every closed edge path of X is 1.

*Proof.* Put B = X/Γ. B is a finite complex, and X → B is a regular covering with deck group Γ, because a free cellular action on a CW complex is properly discontinuous. Fix a base vertex b₀ of B and a lift x₀. Then π₁(X,x₀) ≅ K, the kernel of the surjection π₁(B,b₀) → Γ. Both groups are finitely presented. The kernel of an epimorphism between finitely presented groups is the normal closure of finitely many elements. So K is the normal closure in π₁(B,b₀) of edge loops k₁,…,k_m. Since H₁(X)=0, K is perfect.

For each j, fix an identity in π₁(B,b₀):

k_j = ∏_{t=1}^{T_j} [c_{jt}, d_{jt}],

where each c_{jt} and each d_{jt} is a fixed finite product ∏_s w_s k_{i_s}^{±1} w_s⁻¹ with edge loops w_s. Let N be the largest number of factors in any c_{jt} or d_{jt}. Let ℓ be the largest edge length of the k_j.

Flatness on 2-cells makes holonomy a well-defined homomorphism from π₁(X,x) to U for every vertex x. Changing the base conjugates the holonomy, so |hol(γ)−1| does not depend on the basepoint. For a vertex x over b₀, let k_j^{(x)} be the lift of k_j that starts at x. It is closed because k_j ∈ K, and it has length at most ℓ. Define

δ = sup_{x over b₀, j} |hol(k_j^{(x)}) − 1|.

Then δ ≤ ℓη. The supremum is over infinitely many deck translates, but every term obeys the same length bound.

Lift the fixed identity starting at an arbitrary x over b₀. Loops that are homotopic in B lift to loops that are homotopic in X. A lifted factor w k^{±1} w⁻¹ is a path from x to x', the loop k^{(x')}, and the path back. Its holonomy is a conjugate of hol(k^{(x')})^{±1}, so its distance from 1 is at most δ. Telescoping gives |hol(c̃)−1| ≤ Nδ for every lifted c or d. Expanding ab−ba = (a−1)(b−1)−(b−1)(a−1) and using bi-invariance gives |[a,b]−1| ≤ 2|a−1||b−1|. Hence

|hol(k_j^{(x)}) − 1| ≤ 2 T N² δ²,  with T = max_j T_j.

C = 2TN² does not depend on x or j. Taking the supremum gives δ ≤ Cδ². Choose η < 1/(Cℓ) (any η works when K is trivial). Then δ ≤ ℓη < 1/C, so δ(1−Cδ) ≤ 0 forces δ=0.

Every element of π₁(X,x₀) is a product of lifted conjugates of k_i^{±1}, that is, paths followed by loops k_i^{(x')} and then the return paths. All of these have trivial holonomy, so every closed edge path has trivial holonomy. ∎

**Consequences.**

- Source249's `prop:small-labels` mechanism cannot exist on any free cocompact model of a finitely presented group, with any triangle basis, in any compact unitary group. So `thm:presentation` gives no obstruction for finitely presented groups. This is consistent with source249's G not being finitely presented. It closes the transfer of the source's obstruction to [W_L,W_L], which has finite index in W_L, and to the Leary envelopes discussed below.
- Concrete instance (the prior runner's chamber picture). Let Σ_L be the Davis complex of W_L, with chambers K = cone(L′). Put Y = W·L′, the union of chamber boundaries. Then Σ_L minus the cone points deformation retracts onto Y. The pair (Σ_L, Y) has relative homology ⊕ H̃_{*-1}(L′) = 0, so Y is acyclic. [W_L,W_L] meets every conjugate of a spherical special subgroup trivially, so it acts freely and cocompactly on Y. Here π₁(Y) is normally generated by the finite perfect chamber groups π₁(wL′). The quadratic isolation then works chamber by chamber.
- Contrast with source249: in its non-finitely-presented G, the loops carrying holonomy are scaled copies of loops of L of unbounded length. Exactly this escapes the uniform δ ≤ Cδ² argument.

This proposition is a method limitation. It is not a nominee, and it does not refute that [W_L,W_L] could have gd 3.

## 3. The finitely presented route via Leary envelopes is already recorded history

Actual i07-structures Candidate B (history copy 01) already records the following. Leary, *Subgroups of almost finitely presented groups*, Math. Ann. 2018, Theorem 3.4, gives a finitely presented overgroup with cd ≤ cd G + 2, not cd G. Theorem 3.3 applies only to special HNN extensions of free groups. I re-read Theorems 3.2–3.4 and the surrounding paragraph in the prior runner's acquisition. Proposition L1 adds that any finitely presented cd-2 envelope could not be detected by source249's transport anyway.

## 4. A twisted tower criterion from source321, and why it is vacuous here

Source321 is `A-Counterexample-to-Walls-D2-Problem-October-6-2026`. Its `thm:tower` (actual statement and `cor:torsion` read) says the following. Let Y be a finite connected complex of dimension at most 2, and let L be a rank-one local system on Y with H₂(Y;L)=0. Then no map from a finite simplicial F with b₁(F;Q)=0 pulls L back to a local system with nontrivial monodromy. Actual structural-r90 screen321 (history copy 02) already credits the rank-r version as a routine adaptation.

**Criterion C (routine compactness transfer).** Let ρ: Γ → C^× satisfy H₂(Γ;C_ρ)=0, and let S ≤ Γ be finitely generated with H₁(S;Q)=0 and ρ|_S ≠ 1. Then Γ has no 2-dimensional K(Γ,1), whatever its number of cells.

*Proof.* Choose finitely many relations in S that make the abelianization finite. This gives a finitely presented Q with b₁(Q)=0 mapping onto S. Map a finite 2-complex F realizing Q into a hypothetical 2-dimensional K(Γ,1) Y. The image lies in a finite connected subcomplex Y₀. Since Y has no 3-cells, H₂(Y₀;L) ⊆ H₂(Y;L) = H₂(Γ;C_ρ) = 0. This contradicts `thm:tower` on Y₀. ∎

This is source-paid composition. It cannot apply to source249's G, to [W_L,W_L] or to [A_L,A_L]. All of these are subgroups of right-angled Artin groups, which are residually torsion-free nilpotent. Every nontrivial finitely generated subgroup S of such a group has a nontrivial finitely generated torsion-free nilpotent quotient. That quotient has infinite abelianization, so b₁(S) ≥ 1.

For type-FL groups with Euler characteristic χ(Γ) ≥ 1 and ρ ≠ 1, we have dim H₂(Γ;C_ρ) = χ + dim H₁ ≥ 1, so the hypothesis fails as well. A torsion-free finitely presented cd-2 group satisfying C would be a finitely presented Eilenberg–Ganea counterexample. That construction is unbuilt, and it is a famous central problem. Source321's own group has an element of order 2, so it gives no cd-2 example.

There is also a necessary condition. If Γ = π₁(B)/K with B a finite 2-complex and the Γ-cover of B acyclic, then the tower theorem on B already rules out any S that lifts to a finitely generated b₁=0 subgroup of π₁(B). Unlike Proposition L1, this lifting condition is not automatic: closing up the needed perfect-commutator witnesses can regress without terminating. This is an observation about the route, not a result.

## 5. Extending to other seeds is a parameter variant

The transport proof (`prop:small-labels`, `lem:trace-normal-form`, `lem:trace-direction`; read in full) and `prop:model` use only these facts: L is finite, flag, acyclic and 2-dimensional, and there is a nontrivial α: π₁(L) → SU(2). So source249 already covers every such L, including flag triangulations of any Poincaré-sphere spine (π₁ is the binary icosahedral group).

Replacing SU(2) by SU(n) would cover every acyclic flag L whose π₁ has a nontrivial finite quotient. That requires the localized degree lemma (`lem:localized-degree`, read in full) for SU(n). The same proof works with a regular torus element of odd prime order: its centralizer is the torus, the action is free off the torus, and the normal blocks are complex linear. This is a literal compiler variant, and I did not pursue it.

For L whose π₁ has no nontrivial finite quotient (for example, a flag triangulation of the acyclic Higman presentation complex), Malcev's theorem gives no nontrivial finite-dimensional unitary representation. The unitary method is then empty, and the needed invariant is wholly unknown.

## 6. Timing

The prior runner (GPT-6 Astra, interrupted by a user stop) acquired the Leary–Petrosyan, Leary-embedding and Fujita primaries and stated the chamber observation. This runner, Factory Droid (Opus 5.5, high), proceeded in this order. It read source249's introduction, degree, transport and presentation-statement sections, the Leary–Petrosyan §5.4–5.6 bodies, and the i07, 063, 250 and 164 histories. It then ran the final alias search, which surfaced source321 (not seen by the prior runner). It acquired and read source321, and only after that derived Criterion C and Proposition L1. No target was ever frozen.
