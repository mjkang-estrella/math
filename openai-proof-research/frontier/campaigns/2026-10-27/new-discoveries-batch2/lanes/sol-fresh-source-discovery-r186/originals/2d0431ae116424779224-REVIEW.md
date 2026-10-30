# Structural196 — independent contribution review, round 1

**Verdict: TECHNICAL, conditional on correctness of the entire unchanged frozen statement. The correctness condition is UNDISCHARGED.** This review assigns no correctness, acceptance, or count grade. It neither modifies the author statement/proof nor proposes a replacement theorem.

The conclusion is at the full scope: every integer q≥3; every positive cover degree d; oriented integral PD4 and ordinary TOP four-manifold models; torsion-free word-hyperbolic G; every model of Q_q and every marking; all nonzero classes of Z/q; and homeomorphisms without an order restriction. The contribution comparison below covers the simultaneous marked/framed chamber and the longer-law identities, as well as the combinatorial spectrum and final transport. It is not a verdict based just on finite coloring.

After paying the actual pinned source proof operations, the residual is a finite iteration of its marked annulus construction and one-leaf contractions, an arity-independent polarization/Nakayama argument, and a cyclic clique calculation. Those operations fit together without an additional construction principle: the root replacement still has two root curves, the retained sibling subtrees supply the same exterior label cancellation, the off-shell residual ring and edge functions do not depend on law arity, and the closing operations depend on the full marked chamber interface, not on two colors. I find no specifically identified closed nonroutine residual. There is no unresolved essential contribution-comparison obligation in this review. This statement does not discharge any independent correctness obligation on the author proof.

## 1. Scope, evidence, and the comparison baseline

I read the entire frozen statement and author proof, all other directly admitted author mathematical files, and the parent assessment and all twelve questions. The author proof is 38,790 bytes, SHA256 e1845bb0d890383d0a70a9a5146795b76b865fe723f25dcfef8541626ba5e985. The frozen statement is 2,277 bytes, SHA256 3c5dc0b976a4ccd9f7978958e56dcd6e3bc60caf502f28906285e08f8c263037. Neither was edited. Parent finite tests and author read claims are not mathematical or priority certificates.

Write N for Source320, MT for its marked-tensor companion, and PD for its PD4 companion, all at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. All operative proofs at that pin are stipulated true. The comparison uses their proof operations, not merely their headline theorems. In particular:

- N `ch:four-tip-model`, `ch:laws`, the exterior-dual calculation, the marked exterior pushout, full middle basis, Poincare pair, and positive filling proofs;
- N `for:cuts`, `for:linear`, and the complete `for:formal-data` proof, including common off-shell lifts and actual-ideal correction;
- N `ten:assignment` and its full arbitrary-loopless-multigraph/law-set proof;
- MT marked geometry, actual edge curvature/gradient comparison, algebraicity, full closed-form comparison appendix, and vertex correction proofs, including the nested geometry figures;
- PD chamber/duality, universal development, support model, marked stable realization, and controlled removal proofs;
- N reflection/repeated-label cover, positive panel gluing, folding extension, support/grid hyperbolicity, and cyclic-height proofs.

The main wrapper and both companion wrappers, theorem introductions, and bibliography interfaces were read. The actual source wrapper is the 2,273-byte blob c9373d9c4502fceb075831196b1ecaba80f39082. All 37 canonical blobs were authenticated against the complete 13,223-entry tree; authentication of PDFs is not semantic PDF reading. Exact canonical paths, pinned raw URLs, blob identities, bytes and hashes are private in `private/canonical-authentication.json`. Actual semantic extents, including partial files, are in `private/reading-ledger.json` and `private/read-displays.jsonl`.

The source's normalizer/Sylow machinery and comparison of unmarked homeomorphism types are not required by the frozen statement and are not paid as if they had been read. The proof uses a full reflection, not the source's additional quotient designed to distinguish different manifold models. No contradiction with external expectations about Borel rigidity is used against the stipulated source.

## 2. The finite law system and exact cyclic spectrum

Fix q≥3. The author has 5q(q−1) plumbing types (s,c,k), with 1≤s<q, 1≤c≤q, 1≤k≤5. Both ports of a type have color c. Hence each color has M=10(q−1) ports. Choosing an ordered pair of distinct ports in each color, independently choosing one of ten conjugators in every slot, and choosing every sign gives

    k_q = [M(M−1)]^q · 10^(2q) · 2^(2q).

This count is a size of a finite installed list, not a distinct-word claim. Keeping duplicate words as separated bodies causes no change to the interface.

The height w assigns s to the plumbing generator of type (s,c,k), zero to nine extra loops, and later zero to all bottom meridians z_j. It is onto because s=1 is present. For d≥q the quotient plumbing graph has vertices Z/d and separately labelled edges (v,s,c,k) from v to v+s. It is loopless. Incoming and outgoing ports at a vertex are distinct lifted edges even when their unoriented endpoints agree; at d=q one must not identify the edges of offsets s and q−s. Every incident set with two distinct edges of each color is represented by an installed body: allocate its two ports to the two ordered combs. Conversely each body gives such a set.

Here is the independent endpoint calculation. If an assignment avoids every such law, let D(v) consist of colors represented by at most one edge assigned to v. This set is nonempty, since otherwise two assigned edges of each color form a forbidden law. If vertices are joined by an offset in {1,…,q−1}, five distinct edges of each color join them. A common deficient color would allow their two endpoints together to receive at most two of these five edges. Thus adjacent deficiency sets are disjoint. Each run of q consecutive vertices is a clique, so its q nonempty disjoint subsets of a q-element set must all be singletons and exhaust the colors. Comparing overlapping runs gives c(v+q)=c(v). The lifted coloring of Z has periods d and q, hence gcd(d,q); injectivity on any q-run forces gcd(d,q)=q.

For q|d, the coloring c(v)=1+(v mod q) has different colors at the two endpoints of every offset edge. Assign that edge to an endpoint whose selected color is not its own color. Every vertex then receives no edge of its selected color. This both avoids all laws and selects disjoint cap types for the geometric positive construction below. Five parallel copies are inherited slack: the argument needs more than two, and their size is not a nonroutine quantitative improvement. The overlap-clique argument supplies exact q-periodicity, not only a chromatic lower bound.

This lemma is applied only for d≥q. If 1≤d<q is forbidden and a model of Q_d existed, its connected cover of degree 1+qL would be a model of Q_D, D=d(1+qL)≥q. But D≡d mod q. The already proved large-degree obstruction then excludes it. No loopless tensor theorem is applied to a graph with loops.

## 3. The simultaneous marked/framed chamber is a finite iteration of the source construction

### 3.1 Marked annuli, basings, and framings

The relevant source assertion is stronger than an abstract grope-to-word correspondence. N proves that a punctured-torus product, with its two basis annuli on opposite faces, is a boundary sum of two longitudinal-annulus collars. It cuts along two disks meeting their own annuli once, obtains a ball with marked rectangles, and restores the handles. It then replaces the two annular collars with upper torus products, extending their disk cuts through the collars and placing joining-tube feet away from those strips. This is the exact local induction needed here.

Maintain the following data at each finite rooted subtree: its attaching product annulus, the marked terminal annuli and terminal disk cuts, connector feet outside those cuts, and chosen paths through the connector tree. Grafting a torus product at one terminal annulus replaces one cut by two cuts and adds one terminal generator. Cutting again leaves a ball. No cycle is added to the connector graph, so there is no additional free generator. The attaching collar is a product interface during this graft. Induction produces a boundary handlebody with precisely r longitudinal terminal annuli and their free basis, for any r-leaf binary tree. Two q-leaf combs attached to the bottom torus are an instance of this operation.

For all finitely many bodies at once, use the source's reserved parallel terminal tubes and disjoint narrow connector arcs in the three-dimensional outside boundary. A finite family of paths can realize the prescribed independent homotopy classes there: one-dimensional paths can be displaced off one another, repeated portions use parallels, and finitely many reserved return strips can be avoided. Their thickened connector trees and the final body surfaces are then separated. These operations do not add handles to X. Only opposite-port terminal caps can meet in its original plumbing charts. This accounts for simultaneous placement, not just separate existence of each comb.

The framing payment must be stated accurately. N's ribbon twist is `(theta,z) -> (theta,phi(theta)z)`, with phi of the required integer degree and equal to 1 near connector feet. Its return collar ends at the fixed core product circle and carries that winding in its normal quotient. The source transports the **complete marked body**, including initial and attaching annuli, before fixing the initial-boundary link and its surface framing. It does not prove that an independently preassigned framed boundary link can be preserved through arbitrary cap twists. The author likewise constructs and then fixes its law-link; its frozen theorem prescribes no earlier embedding of that link. At the inductive graft the outgoing product is the gluing datum, and the source framing/return-collar adjustment is paired with transport of its markings. Thus the comparison uses the same product interface and final marked link. It does not introduce a new operation for changing cap framings relative to an externally prescribed link. Whether the author's literal construction realizes all claimed marked data remains part of the separate full-correctness condition; this contribution review neither substitutes a new link nor silently fixes a framing defect.

With these marked tree paths, the leaf loops are the stipulated c x^epsilon c^(-1). Brunnian deletion is an induction on the actual tree: killing a terminal input kills its adjacent commutator, then its parent, up to the root. The assertion is not that every arbitrary automorphism of the terminal free group preserves Brunnian words. Internal path changes allowed by the constructed tree conjugate its branches and inputs; they preserve this deletion argument and alter only higher weight terms. External, independently chosen conjugators remain part of the leading tensor.

### 3.2 Arbitrary-depth contraction and the exterior group-ring labels

Krushkal–Quinn §§1.2–1.4 and 2.1 supply the total one-leaf contraction for arbitrary finite height. This is a local neighborhood operation, distinct from their main subexponential-group theorem. A chosen leaf at depth h gives 2^h copies of that one cap, with signs indexed by eta_1,…,eta_h. Product collars remain the attaching data. A discarded sibling is discarded from the contracted disk, not from the ambient exterior.

Remove only the bottom tubes. All upper surfaces and caps remain in E. For each bottom, contract one a-leaf to f and one b-leaf to C, and compress the normal-circle torus over b using C^+ and C^−. The retained rim arc crosses the a-collar once in the original `(s,t,r,theta)` chart; this gives the distinguished coefficient 1. Different body collars do not create such intersections.

For every other terminal intersection in a rim sphere, fix the outer sign epsilon, all earlier eta indices, and the opposing sheet. Pair only eta_h=+ with eta_h=−. The two paths coincide to the final split. Their difference is the whiskered sibling attaching loop followed by an upper normal turn. The sibling capped subtree is still in E and contracts to a null-homotopy there. The upper turn also bounds there because the upper surface was not deleted. Therefore the group labels agree in pi_1(E), while the signs epsilon·eta_1···eta_h are opposite. This proves cancellation for each fixed opposing sheet, including one on another rim sphere. No comparison of epsilon=+ with epsilon=− is needed; such a comparison could contain a nontrivial bottom meridian and would be invalid.

Consequently the source calculation extends by the same last-split pairing to

    lambda(f_i,g_j)=delta_ij,   lambda(g_i,g_j)=0

in the actual exterior group ring. Each individual chosen cap has no self-plumbing; its parallel copies and product bands give the individually embedded framed contracted disk and rim sphere of the source construction. When all selected core types are disjoint, the same neighborhoods give geometrically disjoint pairs except at their designated single intersections. This is the positive-case refinement, not a deduction from algebraic cancellation alone.

KQ explicitly warns that two loose transverse gropes associated to dual caps cannot both be used without additional intersections. That warning is compatible with the operation here: the root a-disk and one b-rim sphere retain their distinguished intersection, and all additional intersections are calculated as above. No simultaneous pair of disjoint loose transverse gropes is being inferred. PRT Lemma 3.4 concerns symmetric-contraction homotopy classes; it does not itself supply the marked exterior group-ring cancellation. Those labels are paid by N/MT's rim calculation plus the retained-sibling induction.

### 3.3 Full middle module and Poincare duality

The bottom replacement is unchanged by the number of upper stages. Its marked pushout is

    E ≃ X ∪_(disjoint F_j) (disjoint F_j×S^1).

The circle and side maps are the actual normal-circle maps, not merely an abstract equivalence. Each F_j maps trivially up to homotopy into graph-type X, because both its root branches have capped contractions. Replacing its side by V_j×S^1, compressing a_j, adds the cofiber S^1_z ∨ S^2 ∨ S^2: cancel the b one/two-cell pair and the remaining torus two-cell has trivial attaching word. Thus

    H = pi_1(X) * F(z_1,…,z_kq),
    D ≃ BH ∨ (2 k_q copies of S^2).

The quotient killing precisely the z_j restores the old outside marking. This is why w(z_j)=0 and the surgery can later be undone in every cover.

Close f_j by the replacement meridian disk to obtain u_j. Matching compression framings give even normal parity. The u–g pairing is the identity and the g–g pairing zero over ZH. The u–u matrix is Hermitian. Remove a triangular half off its diagonal and write each diagonal as z+bar(z): inverse pairs have distinct elements in the torsion-free free group, and the identity coefficient is even. Tubing into the g's realizes the adjusted hyperbolic classes. After choosing Euler number zero, their full Wall quadratic invariant has zero symmetrization. In the quotient identifying g with g^(-1), **retaining the identity coefficient**, symmetrization is injective here, so that invariant vanishes. A reduced quadratic assertion alone would not establish this framed interface.

These classes give the entire basis. Their square matrix in the already known free module of rank 2k_q has a left inverse from the nonsingular pairing. In every finite quotient of H, the complex regular representation makes that a right inverse as well. Residual finiteness separates the finite support of any nonzero reverse-error entry, proving the right-inverse identity over ZH. This is a rank-and-direct-finiteness argument, not cancellation of a possibly nonfree complementary module.

Attaching the basis three-cells kills exactly those free middle summands in both absolute and relative chain homology and introduces no new third homology. Cohomology pulls back to their annihilators. The cap-product identity for (D,S)→(P,S) descends its duality to these quotients/annihilators. The finite free regular-coefficient chain criterion gives all local coefficients. Hence P≃BH is an oriented PD4 pair with unchanged S. Its regular-coefficient H_1(P,S) and H_0(P,S) vanish; H_0(S;ZH)→Z being an isomorphism means the boundary image has one coset, so pi_1(S)→H is onto. In degree d the connected boundary and full lifted d k_q-plane basis meet the same interface. Nothing in these calculations uses law arity.

### 3.4 Positive marked fillings

For q|d select, in both root combs at v, the leaf of color 1+(v mod q). The ends of every plumbing edge have distinct selected colors. Since both of its ports have one fixed color, at most one end can select that core type. All selected caps are therefore mutually disjoint; repeated occurrences use product parallels. One-leaf contractions then give the full geometric hyperbolic system, with disjoint punctured S^2×S^2 neighborhoods.

Replace those neighborhoods by balls. Their simply connected pieces and S^3 boundaries preserve pi_1. In the universal cover the Mayer–Vietoris calculation deletes exactly the full middle module. The degree-three and degree-four terms cancel against the boundary-sphere terms just as for the original punctured products; they do not leave an unexamined new H_3. The remaining cover is simply connected and acyclic, hence contractible. The original map to aspherical P_d extends over each ball since its attaching S^3 maps trivially. Its boundary map and collar are unchanged, or made equal to the specified map by collar homotopy extension. Orientation is retained. This supplies the required marked filling for every multiple, not merely an unmarked manifold with the correct ordinary homology.

## 4. Connected cuts and actual longer-law ideals

### 4.1 The same graph-type and linear input

Suppose a marked filling of S_d exists, d≥q. Attaching the dual surgery two-handles kills exactly the individually lifted z_j free factors, not arbitrary elements of the filling group. The graph comparison therefore cancels those one/two-cell pairs and restores W≃X_d with the original boundary marking. The handle cocores supply the actual law disks. This uses the side marking from §3.3; knowing only the abstract free group would not suffice.

Take the cover obtained by forgetting the extra letters. Its plumbing graph is the original free-group tree, independently of the later cyclic height quotient. Extend the prescribed map on outside faces, torus collars, and disk neighborhoods by the contractible associated-tree-fiber argument. After punctured smoothing and regular-level cutting, the component graph has fundamental group generated by images of the boundary extra loops. Each lies within one vertex piece, so the component graph is a tree. Target vertex-star labels show that the principal plumbing tree is embedded. A stabilizer of a hanging branch fixes its nearest principal vertex, hence is trivial. There are finitely many component orbits; thus the hanging trees have finite valence and bounded depth and are finite. Merge them into the principal pieces. This obtains connected cuts and connected vertices equivariantly. Large height values s and multiple edges in the final quotient change none of this argument.

The TOP filling need not be smooth. The PD puncture-form complex takes functions separately constant near each puncture and positive-degree forms vanishing there. It is a fine resolution of the filled constant sheaf. Every fixed coefficient in the formal construction has support in a compact smooth subdomain, so Stokes has no contribution at the punctures. There need not be a single vanishing neighborhood for an infinite formal series. Fundamental groups and based gauges retain the filled markings. The compact cut three-manifolds themselves remain smooth and are the only spaces to which the marked edge-algebraicity theorem is applied.

Mayer–Vietoris on the finite quotient gives

    Δ2 : ⊕_v H²(V_v) ≅ ⊕_e H²(Y_e),
    Δ1 : ⊕_v H¹(V_v) -> ⊕_e H¹(Y_e) onto.

The first uses H²(W)=H³(W)=0. The kernel of Δ1 is H¹(W)/H¹(Gamma), identified with the 9d extra-loop evaluations. Restricting to zero extra evaluations removes exactly that kernel. Half-lives/half-dies on a single boundary torus gives a one-dimensional image. If both original coordinate loops survived, the longitude vanishing on either side would force each vertex restriction to kill both; Δ1-surjectivity would then be impossible. Thus one original coordinate is killed and the other survives. This establishes the actual endpoint designation, not an arbitrary rational slope choice.

Remove also the plus-end meridian evaluations in the vertex variables. The combined internal tangent difference is an isomorphism; the injectivity of Δ2, together with edge duality, yields the full-column gradient/residual minor. These are exactly the linear hypotheses of the source formal construction. There is no positive-middle-homology defect to absorb here. In particular this is not an extension of that construction to arbitrary stabilized W.

### 4.2 Nonzero tensor and independent polarization

Let B_q be the right-nested bracket with q inputs, and

    T_q(X_1,…,X_q,Y_1,…,Y_q)
        = [B_q(X_1,…,X_q), B_q(Y_1,…,Y_q)].

It is multilinear in 2q independent slots. For the usual sl_2 basis [h,e]=2e, [h,f]=−2f, [e,f]=h,

    B_q(h,…,h,e)=2^(q−1)e,
    B_q(h,…,h,f)=(−2)^(q−1)f,
    T_q = (−1)^(q−1) 2^(2q−2) h ≠ 0.

This nonzero value suffices; one does not need a classification of Lie polynomial identities as q grows. Signs and internal tree basings preserve the lowest nonzero multidegree as described in §3.1.

The source already uses the identity and eight nonidentity elements among exp(aσe)exp(bσf), a,b∈{0,1,2}. Their nine adjoint matrices span End(sl_2) over C((σ)); the determinant calculated in the source is 512σ^18. Eight extra loops realize the nonidentity matrices and the ninth is harmless reserve. Thus the number of loop generators need not grow with 2q. Independence is across slots: different slots can use the same list of nine matrices with independent choices. The full finite law list contains all those choices.

For a nonzero multilinear tensor T on V^r, precomposition independently by End(V) in all r slots and evaluation by a nonzero output functional span all scalar multilinear forms. Indeed choose inputs u_1,…,u_r with T(u_1,…,u_r)≠0; for any coordinate functionals α_i take the rank-one maps x↦α_i(x)u_i and an output functional nonzero on T(u_1,…,u_r). Their value is a nonzero scalar times ∏α_i(x_i). Expansion in the nine-adjoint basis supplies the requisite linear combinations of installed tests. This elementary argument in N's formal proof has no four-slot restriction.

### 4.3 Exact ideals off shell

Work in one vertex's complete Noetherian local ring with all squarefree parameters retained. Fix the source's residual curvature list and let I_v be its ideal. Choose one off-shell lift X_e of each flat-quotient port logarithm, once for the entire family of independently conjugated laws. For a law set L put

    J_L = ∏_(e in L) (coordinates of X_e),
    Q_L = ideal of all scalar entries of its installed law logarithms.

On the quotient by I_v, the curvature is zero, holonomy is genuinely flat, the prescribed law disks give exact relations, and the chosen logarithm lifts have the required marked meanings. Consequently Q_L⊆I_v. Off shell one evaluates the formal words on these common lifts; one does not assert that path homotopies preserve arbitrary off-shell parallel transport. Tree deletion puts every term in every slot ideal, hence Q_L⊆J_L. All terms beyond the leading multilinear term lie in m J_L. Variations of conjugators from their fixed background values also contribute there. The rank-one calculation above then gives

    J_L = Q_L + m J_L.

The module J_L/Q_L is finite. Nakayama yields J_L=Q_L and therefore J_L⊆I_v. This argument works in the actual nonreduced ring. It uses neither radical membership nor flatness of its critical quotient. Its arity dependence consists only of the finite number of factors in J_L and tests in Q_L. The same common-lift requirement was already enforced in N; separate lifts chosen independently for each conjugator would not give this comparison.

At plus endpoints the prescribed logarithm is the parameter times the chosen fixed matrix; at minus endpoints its paired scalar is the marked holonomy weight. The preceding product ideal therefore gives exactly

    (∏_(e in L∩E_+(v)) t_e)
    (∏_(e in L∩E_−(v)) b_e) ∈ restricted actual gradient ideal.

Both pure and mixed endpoint cases are covered, including empty products. The number of slots does not change the surrounding edge problem.

### 4.4 Common algebraic edges, correction, and the tensor theorem

Here the strongest payment is substantial and must not be silently replaced by a standard reduced deformation-space argument. MT constructs an edge potential whose full gradient ideal equals its curvature ideal. Its algebraic chart comparison uses the full relative closed shifted form, not just an identification of classical loci. The appendix gives the source-cochain/derived-coefficient trace comparison. The induced formal coordinate change fixes the entire critical scheme and marked holonomies; its correction lies in the square of the actual gradient ideal. These read proof operations are stipulated and paid, not newly claimed for r196.

The vertex construction keeps a fixed list of residuals, although they need not form a regular sequence. The curvature recursion expresses all curvature in that list. Coefficientwise Stokes puts the restricted sum of edge potentials in I_v². The gradient is Lr with a full-column minor at the joint origin, from §4.1. The source's section correction cancels that square-ideal error while preserving the quotient, residual ideal, and central tangent. A shared edge has one set of algebraic coordinates and functions; independently selected vertex charts are not substituted for it.

Joint recentering along the free flat background occurs before passage to C((σ)). The required minor remains a unit there. The comparison does not claim that the recentered Hessian still vanishes. For polynomial holonomy replacement use the same quadratic logarithm truncation of G−1 as the source. Setting only an edge's own t_e to zero leaves its plus holonomy error in I_v while all other parameters remain. Thus its weighted remainder has orders t_e I_v³ and its internal derivative t_e I_v². The source finite nilpotent correction takes an error in t^n I_v² to one in t^(2n) I_v² by a displacement in t^n I_v. It preserves the residual ideal and quotient, common edges and central tangents. Since the full ideal t is nilpotent, it terminates. Keeping each t_e²=0 does not permit discarding mixed products t_e t_f; they are essential both here and in the tensor argument.

The result is exactly N `ten:assignment` for the graph in §2. Its proof, read in full, handles arbitrary law subsets at each vertex. Ordinary Artin approximation applies to a finite coefficient system with fixed separated algebraic edge functions and common vertex variables; it is not nested approximation of unknown separated potentials. Finite specialization preserves units, tangents and witnessed ideal memberships. In positive characteristic, graph forms in truncated coordinates have global pairing ±det(C)^p≠0. Actual gradient memberships become actual Koszul boundary identities. The second differential is induced by exterior differentiation. A compatible projection preserves the multiplication-kernel representatives, although these kernels need not themselves be subcomplexes. Tensoring the individual parameter lifts retains mixed terms; a nonzero pairing yields an endpoint choice avoiding every installed law. No regular-sequence or critical-point-isolation hypothesis enters.

This pays the passage from longer Brunnian words to the full endpoint theorem, not just a leading-term obstruction on tangent spaces. Combining that theorem with §2 excludes marked fillings for all d≥q with q∤d.

## 5. Closing the chamber, hyperbolicity, and every model

### 5.1 Reflection and the controlled filling implication

Every covered chamber has connected collared boundary, a free group with the specified boundary epimorphism, graph plus a full even framed hyperbolic middle module, zero full quadratic invariants, and the oriented PD pair obtained by the basis attachments. These are the actual hypotheses of N `refl:input`, not a general slogan that reflection preserves obstruction.

PD's proof of the filling implication has two distinct models and a marked stability step. The support CAT(0) model supplies assembly. Its chamber development supplies four-dimensional topology and the labelled sphere systems. The full regular-coefficient hyperbolic module and fundamental class are used to produce an integral marked homotopy equivalence with a hypothetical model plus standard planes. Marked bordism and the stable product preserve the specified sphere classes, not only an unmarked stable homeomorphism. Periodic lifts give finitely many local patterns and bounded propagation for those finite data.

In a large finite chamber union, complementary fillings cap all boundary factors except the central one; the shelling calculation retains the central H-marking. Peeling standard inner neighborhoods removes the inner planes. The remaining prepared systems are far out, where a bounded carrier has small radial image in the central boundary S. The estimate is d(rho(x),rho(y))≤(2t/s)d(x,y). Projection to BH of that direction map agrees with the central-factor marking, including across the far-out replacement balls.

The crucial control is of entire upper image systems. The first separation phase groups upper components into finitely many coordinate patches, with bounded propagation depending on that fixed cover. The second separates components within each disjoint patch neighborhood; it needs no bound depending on their number. All loops in each resulting cap image map into a contractible patch and hence are null in Z. Protected Clifford capped surfaces and retained lower stages stay unchanged. Geometric duals give pi_1 of the relevant complement equal to pi_1(Z), so these loops are null in the complement as required. This supplies the specific null-loop input used after goodness in PRT Lemma 4.2. Subsequent null-homotopies and tower caps may range through Z; a false uniform-control conclusion is unnecessary. PRT's final tower/Whitney operations and duals yield framed embedded Lagrangian spheres. The surgery trace removes the remaining regular-coefficient planes and preserves the central marking, giving a graph-type filling.

The primary PRT §§4–5 proof was read as well as §3. It explicitly locates goodness in the initial upper replacement of Lemma 4.2; the following collar-protected dual construction uses the resulting null loops. PD supplies that input by its own stipulated control operation. R196 neither assumes free groups are good nor contributes a new unrestricted disk theorem. Its larger finite rank and number of planes change finite preparation sizes and bounds, not the hypotheses or mechanism. This is the correct strongest compatible payment for reflection-to-filling.

### 5.2 Repeated labels and positive closed models

Use a flag-no-square triangulation of S and the full original independent label group A_0. The folding map extends height to the reflected group and defines Q_d. In Q_d each lifted boundary vertex retains its original label. It is therefore a repeated-original-label reflection of P_d, rather than already the full reflection with independently labelled lifted vertices.

Let A_d have one independent generator per lifted vertex and map A_d→A_0 by forgetting the lift. On the label subgroup of a face, this map is injective: a simplex projects to a simplex and its distinct vertices have distinct original labels. Stabilizers in the actual development are exactly these face subgroups. Hence the kernel acts freely there. This proves a genuine finite cover from the full reflection of P_d to Q_d, even though no claim of torsion-freeness for the entire abstract kernel is needed. A manifold model of Q_d pulls back to a model of that full reflection, and `refl:input` then gives the prohibited marked filling. This excludes every closed model, not merely models respecting visible chambers.

For q|d, replace each chamber by the marked filling of §3.4. Near an r-fold panel intersection the 2^r sectors are the source orthant charts; there is no local label identification because of the same face-injectivity property. In the source's coordinates one may use x_i=t+max_j d_j−d_i, with inverse t=min_i x_i and d_i=mean_j x_j−x_i. These local charts supply the TOP manifold structure. Alternating orientation by original independent labels makes panel gluings oriented. Cofibration homotopy pushouts replace finitely many chamber equivalences relative to their boundary maps, yielding a closed connected manifold homotopy equivalent to Q_d. The transported orientation makes that equivalence degree +1. Together with §2's lifting argument this gives the entire claimed cover spectrum.

### 5.3 The group assumptions

The lifted nerve has finitely many H-orbits but infinitely many vertices. It would be insufficient simply to call its Davis complex cocompact. The paid support construction chooses equivariant anchors in the free-group Cayley tree and finite-radius subtrees T_u, with adjacent supports intersecting. A fixed tree vertex belongs to a uniformly finite set of supports. Special Coxeter groups on those finite induced sets, and on their intersections across a tree edge, have colimit the required Coxeter group: connected supports identify each generator, and every defining commutation occurs somewhere without adding extra relations. Convex gluing of their Davis complexes over the Bass–Serre tree is CAT(0), locally finite, proper and cocompact for the semidirect product E. Dimension is at most five. This is not the ordinary chamber development used in §5.1.

The no-square nerve gives the source grid bound. Opposite edges of a combinatorial square have the same labels. One direction of an isometric grid has no tree labels. If it is long enough, it contains two noncommuting Coxeter labels; then the other-direction Coxeter labels form a clique, since two noncommuting ones there would make an induced four-cycle. Such a clique has at most four vertices, giving at most 16 Coxeter coordinates. The fixed label in the first direction confines tree coordinates of a crossing line to its bounded support, of cardinality at most b_T. Thus grid sides are uniformly bounded (the source bound is 16b_T−1). The median-grid argument supplies thin triangles. E is word-hyperbolic; its finite-index reflected subgroup G is too. Constants may depend on q. Neither color counts nor numeric values of w occur in this proof.

The folding homomorphism restricts to the identity on H⊂G, so eta is onto. The finite four-dimensional aspherical complex gives finite integral cohomological dimension. A nontrivial finite-order element would give a finite cyclic subgroup with nonzero integral cohomology in arbitrarily high degrees, incompatible with restriction of a finite free resolution. Hence G is torsion-free. All of this uses the same finite chamber/nerve inputs, not a new hyperbolization theorem.

### 5.4 Every model, every marking, unrestricted order

Put K=ker eta. For gamma of height one, G_q=K⋊<gamma^q>. Conjugation by gamma preserves G_q and its q-th power is inner there. Changing gamma to gamma' of height one changes it by an element of K⊂G_q, so its outer class, and the whole homomorphism Z/q→Out(G_q), are unchanged. Changing the marking u transports it by the induced outer isomorphism. Deck transformations of the oriented cover Q_q→Q represent all its classes by degree +1 homotopy equivalences; an equivalence with any marked N transports these classes and orientations.

The source's cyclic criterion has an unrestricted-order argument, which extends verbatim in its arithmetic to every nonzero residue a. Suppose a homeomorphism h of any N≃Q_q induces [Ad gamma^a], 0<a<q. Correct a universal-cover lift by an inner deck transformation to obtain exact conjugation by gamma^a on G_q. It descends to the K-cover N_K and commutes with T induced by gamma^q. Choose a proper T-equivariant height p:N_K→R with p(Tx)=p(x)+1; compactness of N supplies it from a compact fundamental region. The displacement of the descended h' is T-periodic, hence bounded by C.

For an integer R>C+1, F=T^R h' satisfies

    R−C ≤ p(Fx)−p(x) ≤ R+C.

These inequalities prove three separate facts. No nonzero iterate fixes a point, so the action is free. Iterated heights escape any compact height interval in either direction, so it is properly discontinuous. Every orbit meets a fixed bounded-height band, whose inverse image is compact, so the quotient is cocompact. It is consequently a closed TOP four-manifold with the contractible universal cover of N.

Its deck group is K⋊Z, where the new stable letter acts by Ad gamma^(qR+a). There is no hidden relation: the descended F-action is infinite free, so any deck word trivial on the cover has zero stable-letter exponent and then is trivial in K. Equivalently the proposed map t↦gamma^(qR+a), k↦k is injective by height and onto G_(qR+a). The quotient is a manifold model of Q_(qR+a), contradicting its nondivisible degree. If h merely induces the specified outer class, asphericity makes its homotopy class the specified degree +1 class, so no orientation-reversing exception occurs. No assumption about h's order was used.

If a nonzero residue gave the identity outer class, the identity homeomorphism would be the forbidden h. Thus the homomorphism is injective. The identification of homotopy classes of self-equivalences of an aspherical model with its outer automorphisms gives exact order q, and reduction modulo q deals equally with negative powers of a homotopy inverse. This applies to every model and marking, independently of how the positive construction produced one model. The passage from eventual exclusions to all classes is already the source height mechanism, not finite-group Nielsen obstruction alone.

## 6. Actual primary and original-history comparison

### 6.1 Primary proofs, versions, and limits of their payment

The six primary PDFs were independently retrieved to this review's private root. Each matches the author's PDF byte-for-byte, and independent `pdftotext -layout` output matches its text. Retrieval and matching are authentication only; semantic ranges are separately recorded. The original proofs, not abstracts or another review's summaries, support the following comparisons.

**Block–Weinberger (2008), §§1–2, entire paper read.** Their [published paper](https://ems.press/doi/pdf/10.4171/CMH/116) constructs homotopy actions by gluing boundary actions that agree homotopically but differ geometrically. The surgery construction retains a relative UNil obstruction after hyperbolization and gluing; a finite cover kills that obstruction. Their proof of Theorem 1.6 uses Smith theory and low-dimensional fixed-set recognition to turn the required Z/2 fixed sets into manifolds, excluding the action. The odd-prime embedding construction in §2.2 instead obstructs an equivariant manifold model under fixed-set assumptions and explicitly does not supply their full Nielsen conclusion. Proposition 1.2's torsion-free-extension realization uses dimension at least five and total surgery. These are genuine predecessors for finite actions and cover behavior. They do not prove individual nonrealization of homeomorphisms of arbitrary order in dimension four. N's height argument supplies that stronger operation; it cannot be replaced by citing BW alone.

**Krushkal–Quinn (2000), §§1.2–1.4 and 2.1.** The [original paper](https://uva.theopenscholar.com/files/slava-krushkal/files/subexponential_groups.pdf) explicitly describes total contraction down a chosen branch and the 2^h multiplicity of a tip at depth h. Its transverse-grope discussion warns that the constructions from two dual caps intersect. These are the local operation and limitation used in §3.2. The main disk-improvement theorem assumes subexponential growth; no such theorem is applied to the free chamber group. Increasing q asks for a longer finite tree, which this local operation already permits. Its use with the marked root and exterior labels is supplied by the N/MT constructions, not by omitting those labels from KQ's statement.

**Powell–Ray–Teichner (2025), Theorem A, §3 including Lemma 3.4, §§4–5.** The [published version](https://www.maths.gla.ac.uk/~mpowell/s00029-025-01069-y.pdf) assumes a good fundamental group for Theorem A, preserves input boundary framings, and constructs geometric dual spheres with controlled homotopy classes. Its symmetric-contraction lemma handles independence of cap choices. Lemma 4.2's proof uses goodness to produce upper disks with null double-point loops, then uses protected collar levels, contractions, pushdowns and tubing to construct towers with geometric duals. Section 5 uses these duals to keep the original spheres away from Whitney towers. This is stronger proof information than a generic invocation of disk embedding. PD pays its particular substitute for the null-loop step and the later marked removal; r196 has the same input. No conclusion that a nonabelian free group is good is needed or justified.

**Davis–Lueck, arXiv:2303.15765v4 (26 January 2024).** The actual [v4 proof](https://arxiv.org/pdf/2303.15765v4), Theorem 1.16 and §8, supplies high-dimensional proper manifold models under finite-extension, slice and assembly hypotheses. Theorem 6.3 uses transfer of the total surgery obstruction for a pair to obtain its manifold replacement; §8 proves the required transfer injectivity through structure-group and assembly calculations. Its realization range is d≥5, with special good finite-group handling of the four-dimensional boundary when d=5; Theorem 6.3 itself is stated for d≥6. That is not a theorem for a four-dimensional interior pair with arbitrary free group. Its assembly/transfer strategy is a strong comparison, but neither closes a four-dimensional realization here nor invalidates the stipulated source.

**Hilman–Kirstein–Kremer, arXiv:2409.02220v1 (3 September 2024).** In the [v1 proof](https://arxiv.org/pdf/2409.02220v1), Theorem A invokes the Davis–Lueck manifold result for odd prime, pseudofree extensions of high-dimensional hyperbolic manifold groups. Section 5.1 identifies the fixed-space components through Weyl groups and proves genuine virtual Poincare duality. Section 5.2 proves Condition (H) via the gluing class, dualizing spectra and the Tate boundary: its linearization generates each Z/p summand. These actual arguments remove a homological compatibility condition within that framework. They do not remove the dimension restriction on the invoked manifold-realization step, and they do not address arbitrary q or the individual unrestricted-order conclusion in this four-dimensional target.

**Kremer, arXiv:2608.30620v1 (31 August 2026; PDF dated 1 September).** The [v1 Theorem B and §6.2 proof](https://arxiv.org/pdf/2608.30620v1) concern oriented aspherical d-manifolds with d≥6, hyperbolic fundamental group, odd-prime cyclic action, and a PL model for homotopy fixed points of dimension ≤(d−2)/2. The proof transfers a total surgery obstruction to a cover, uses injectivity to obtain a manifold pair, and uses an approximate fibration and teardrop construction to attach the fixed manifold. High-dimensional Borel rigidity transports the action to the given model. This improves the allowable fixed-set dimension, not the ambient four-dimensional category. I do not treat it as a four-dimensional theorem.

These readings establish the operative distinctions essential to contribution, not worldwide literature clearance. Recursive proofs of every classical theorem cited in the pinned papers were not separately downloaded. Their operative uses in the read, stipulated source proofs are paid at precisely those interfaces. In particular algebraic Darboux/trace theory is paid through MT's actual comparison proof, and stable/control surgery through PD's actual proofs, rather than asserted from unrelated primary headlines.

### 6.2 Original history, without inherited dispositions

I authenticated the author's selected copies against the admitted original spans and read the original bytes, bounded by their next equal/higher headings:

- `frontier/iterations/i07-structures.md` [7520,40912): Candidate E and the following operative sections through the next `## 9` heading boundary;
- `frontier/iterations/i97-relative-involution-stabilization.md` [1222,11173): original source object, relative nonextension and stabilization scope, through the next `## 3` boundary;
- that same I97 file [25116,30416): the middle-homology cut-defect argument, through the next `## 6` boundary.

A one-line next-heading lookahead was used only to authenticate the endpoint; no following section body was read. These are the only original-history bodies selected. Earlier author prefixes crossing derivative prose were not used as premises. Some disposition/grade prose occurs inside the expressly admitted historical spans; it was incidental and is not a premise for this verdict.

**I07's actual scope and mechanism.** Its construction covers every rank for an elementary-abelian 2 group and individual nonrealization of each nonidentity class. It uses channel-indexed colored plumbing, full independently conjugated finite law lists, graph cuts with the same cohomological restriction interface, disjoint selected cap ends, and reflection. Its lattice condition forces coordinate bit behavior under translations, giving the exact compatible-lattice spectrum. Its height transport also treats nonidentity classes individually, with the extra cocycle bookkeeping needed in the nonsplit higher-rank setting. It is not the same theorem as arbitrary cyclic q with hyperbolicity. But it already demonstrates that the general graph/law construction, simultaneous channel choices, exact spectrum and individual transport can be composed. R196's cyclic splitting makes the final height step simpler. I use those original operations, not I07's historical contribution language.

**I97's actual obstruction to an overbroad payment.** Its immutable task fixes a relative involution/stabilized problem; it is not a fresh all-q claim. The relevant cut calculation has positive middle homology: residual dimension dk gives a cokernel defect in degree one and a kernel defect in degree two. For its stabilized regime, the defect can absorb the anomalous slopes/deletions that the parity argument needs to exclude. Connected tree cuts are still available at the group level, but the zero-defect formal tangent theorem cannot simply be applied. This review does not solve or reopen that problem. R196's W is exactly graph-type, with H²=H³=0, and so stays within the source's original zero-defect hypotheses. Avoiding that different problem is not a new middle-defect-removal operation.

No guarded broad history scan was needed beyond these concrete admitted antecedents. This limits claims about project history beyond them. There is no inference that other constructions or stronger precedents do not exist. Such omissions cannot create a substantial residual when the explicitly reconstructed compatible composition already covers the frozen scope.

## 7. Parent-question coverage and the contribution determination

| Parent question | Contribution comparison at the unchanged scope |
|---|---|
| 1. Scope/interfaces | §§1–5 retain every quantifier, TOP/orientation requirements, exact graph marking, and all refl:input/ten:assignment hypotheses. No author correctness grade is assigned. |
| 2. Law coverage/combinatorics | §2 counts the list, distinguishes all parallel lifted edges, proves both directions of q-periodicity, and restricts the loopless application to d≥q. |
| 3. Marked framed placement | §3.1 gives the marked-annulus induction, basis and simultaneous paths, paired framing/return collars, and the distinction between final transported markings and an externally preassigned link. |
| 4. Full exterior pairing | §3.2 fixes epsilon, earlier eta's and the opposing sheet; only the final eta pair cancels using the retained sibling and upper normal turn. KQ's warning is addressed. |
| 5. Full module/duality | §3.3 retains ZH coefficients, full Wall quotient, finite-quotient direct finiteness, whole basis, all-coefficient duality, boundary surjectivity and height-zero z_j. |
| 6. Positive fillings | §3.4 proves the selected-core criterion, geometric pairs, full-module deletion, asphericity, orientations and exact boundary marking in every multiple. |
| 7. Cuts/linear input | §4.1 supplies the principal/component-tree argument, finite hanging branches, TOP puncture complex, 9d evaluation kernel and zero-defect tangent input. |
| 8. Longer actual ideals | §§4.2–4.4 give nonzero T_q, independent rank-one polarization, common off-shell lifts, Q_L⊆J_L∩I_v, Nakayama, actual mixed memberships, common algebraic edges and finite correction. |
| 9. Reflection/all degrees | §§5.1–5.2 verify the actual input and stable/control mechanism, face-stabilizer freeness for repeated labels, orthant gluing and orientations. §2 treats small degrees by lifting. |
| 10. Group properties | §5.3 pays the support model, bounded grids, finite-index transfer, onto folding character and torsion-freeness without a q-uniform metric claim. |
| 11. Every model/class | §5.4 proves the marking/gamma assertions, exact lift, height bounds, separate free/proper/cocompact facts, quotient group with no hidden relation, all residues and negative powers. |
| 12. Entire-scope contribution | §§2–6 reconstruct the integrated paid construction, including actual primary and original-history proofs, before assigning the conditional TECHNICAL verdict. |

The remaining finite iteration is not merely an invocation of an unread difficult lemma. Its invariant data and the algebraic compatibility are recorded above. Conversely, the proof's length, the size k_q, and the dramatic TOP4 statement do not themselves identify a nonroutine residual relative to the unusually strong stipulated source package.

The strongest candidate for such a residual is the simultaneous arbitrary-depth, multicolor, marked/framed chamber. Once the source's actual annulus proof, retained-sibling exterior calculation and classical total contraction are paid, its construction is the same finite graft repeated at terminal annuli. Its full middle module is still controlled solely by the bottom replacement. The strongest algebraic candidate is the longer-law membership in actual gradient ideals; the fixed-lift/polarization/Nakayama proof has arbitrary arity, and all edge, Stokes, recentering and nilpotent corrections are unchanged. Finally, exact all-degree spectrum comes from overlapping q-cliques and cover lifting, while every-model unrestricted-order nonrealization is the same height operation for qR+a. Their compatibility is essential and has been checked for this comparison; none supplies a closed nonroutine residual beyond those payments.

Therefore **TECHNICAL is the contribution verdict for the entire unchanged frozen statement, conditional on full correctness.** This is not a recommendation to narrow the statement and not a favorable-grade retry. If the parent does not independently adopt whole-scope correctness, this conditional review does not make the author result usable. No acceptance or count is assigned here.

## 8. Reading, isolation, and integrity limits

All writes, downloads, renderings and scratch were confined to this exclusive review root. Every command used the actual project root as workdir. There were no nested agents, git/staging/commit operations, peer status reads, browser UI actions, public actions, or downstream manuscript/formal/release work.

Before non-direct selection or traversal, I installed every listed literal wildcard individually, all corresponding no-r twins, all full-path casefolded substring exclusions including `publication` and plain `check`, and the explicit derivative patterns. Own-root files were excluded from broad authored-history scans. The installation records 169 literal wildcards, 169 compared twins and 150 substrings. Exact author/parent and receipt-directed canonical/primary/history admissions were used as file or span exceptions; they did not admit containing directories. The only author-root inventory traversal was the expressly permitted read-only integrity replay. No foreign review or arithmetic162 body/status was inspected, and no structural195 body was read or reopened.

These are prospective prompt-level filters, not operating-system isolation or perfect semantic classification. They can omit useful originals and fail on opaque aliases. No broad discovery traversal was run, so there are no observed lexical false admissions from such a scan and no exhaustive clearance claim. Incidental historical disposition prose within the admitted spans and the author's disclosed earlier derivative crossings are expressly excluded as mathematical premises.

The exact initial metadata output had a truncated navigation display, and an author reading-ledger prefix was deliberately displayed only as navigation. Neither is credited as proof reading. Subsequent selected mathematical displays were bounded and complete at the recorded ranges; partial file selections remain partial. The own ledger records byte extents, character extents, duplicate reads and range hashes rather than inheriting the author's read certificate. All reviewer reads necessarily occurred after the author's freeze; no later source version was substituted.

Primary access succeeded for all six selected PDFs. Text extraction contains control/glyph artifacts; Kremer's PDF produced a font-type mismatch warning. I visually inspected the PRT page containing §3.4 (PDF page 14) and KQ §2.1 (PDF page 7, printed page 413), recovering the contraction notation, including 2^h rather than the flattened text's apparent `2h`. The remaining pages were not visually audited. No semantic reading of the canonical source PDFs is claimed; canonical TeX supplied that reading. The MT wrapper's system `glyphtounicode` input remains a nonmathematical unresolved utility, not a missing proof include. Bibliographies identify further references; reading their entries is not reading those references.

The supplied author FINAL/MANIFEST/REPORT anchors and the frozen/proof bytes matched. A read-only replay of the author's verifier succeeded on its 78 selected files; an integrity-only inventory found 85 files. Its code does not reject extra unselected files and does not bind modes. I did not repair it or represent it as doing so. The before/after inventory comparison of the author root records preservation of bytes and modes during this review's finalization; it is an artifact observation, not proof.

This review seals its own exact selection once. Its verifier requires explicit detached FINAL/MANIFEST/REPORT hashes, checks all selected bytes and file/directory modes, rejects symlinks and extra/missing selection, and validates the detached anchor carrier. Small copied fixtures exercise byte, exact-selection and mode failures. Protected bodies, renderings, copied controls and named metadata remain private/local under their original rights. The outside REPORT is a detached carrier in this exclusive root; it is not a publication. Integrity checks establish only the packet's identity.
