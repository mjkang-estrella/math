# r204 working mathematical derivations — prefreeze

Provenance: Codex / GPT-6 Astra / xhigh / default service tier, as authorized. Source328 and every operative pinned upstream proof at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are premises, not audit targets. No mathematical nominee has been frozen. This is research, not a manuscript or formalization.

## Source interfaces already read in full

Theorem `thm:main` concerns a **real**, complete, reflexive Banach space in its **given norm**, and a nonempty norm-closed bounded convex domain. The map is a single nonexpansive selfmap. Neither separability, strict convexity, normal structure nor weak continuity is assumed. Nonseparable data are reduced to a separable invariant convex subset before minimality. `cor:commuting` already gives a nonempty **nonexpansive retract** for every commuting family, including uncountable families. It is not a new direction here.

The source's stronger usable operations are not just its theorem statement:

* `lem:resolvents`: after diameter-one normalization, R_n(a)=a/n+(1−1/n)TR_n(a), Lip(R_n)≤1, defect≤1/n and displacement≤(n−1)defect(a).
* Finite composition and pointwise convex combinations give G with displacement≤c_G defect(a). Tails H_m={R_n G:n≥m} have **uniform** defect≤1/m.
* `lem:finite-tuples` turns pointwise weak closure of a **convex** family of nonexpansive maps into simultaneous norm approximation at any finite list of arguments. It also proves preservation of nonexpansiveness by weak lower semicontinuity; it does not assert weak continuity of a nonlinear map.
* `prop:anchor`: weak pointwise closed convex tails form compact semigroups, composition being justified by two finite-tuple norm approximations. Ellis gives an idempotent P and x=P(x) lying in the norm-closed convex hull of the weak tail set D_x.
* `lem:adaptive-selection` permits arbitrary history-dependent finite thresholds and terminates with a finite convex average within any prescribed positive tolerance of x. It gives no numerical stopping bound.
* `prop:tree-data` predicts **already evaluated** nonlinear root outputs over a compact coefficient polytope before choosing the next detector. Its norm compactness follows from a uniform coefficient Lipschitz bound, without moving weak limits through nonlinear maps. Zero-weight candidates are retained in the prediction lists.
* `prop:finite-witness`: right-to-left leaf switching gives f_v(U_v−V_v)≥W_v−5e_v. With d_s=(U_s−V_s)/W_s, ||d_s||≤1 and the weighted total deficit is ≤5/128. A branch with all detections >1/2 follows without a lower bound on W_s. Compactness of the **whole unit ball of span(K−K)**, not merely K, gives the infinite witness contradicting pointwise vanishing detectors.

All these operations are credited. Their use of a minimal invariant set and exact nonexpansiveness cannot silently be transferred to approximate dynamics.

## Classical machinery already paid

Bruck 1974, Theorem 1, and its finite-family proof use r:C→F_n and the identity Fix(T r)=F_n∩Fix(T) when T preserves F_n. No convexity of F_n is needed. The infinite-family step uses directed intersections of nonexpansive retracts (Lemmas 1–3), not weak compactness of the fixed sets. Its Theorem 3 is a compact semigroup retraction principle requiring a common fixed point in **each orbit closure**, not just individual fixed points.

Bruck 1975, Theorem 1, requires strict convexity in two places: equality in the midpoint norm estimate turns minimal-range isometries into translations; fixed sets of the resulting retractions are convex, so convex-range intersection yields actual intersection. His final example already prevents deleting strict convexity from the convex-range-intersection criterion, even in R² with the sup norm. For t∈[0,1], f_t(u,v)=(|v|−t,v) on [-1,1]² satisfies f_t f_s=f_t, is nonexpansive, and depends affinely on t. Every closed convex range hull contains (0,0), but different parameters have disjoint fixed ranges. Source328 does not turn this incompatible family into a commuting or common-fixed-point family.

## Asymptotic direction: exact ultrapower reduction

Take a real Banach space X, C nonempty closed bounded convex, and a norm-continuous map T:C→C. Put

    e_n = sup_{u,v∈C}( ||T^n u−T^n v||−||u−v|| ).

Assume e_n→0 (e_n≥0 by u=v). This is the intermediate-sense asymptotic nonexpansiveness used in Wiśnicki 2012, not an assumed rate. For a free ultrafilter U and any increasing α_i→∞, define

    S_α[(x_i)] = [(T^{α_i}x_i)] on C_U⊂X_U.

The inequality ||T^{α_i}x_i−T^{α_i}y_i||≤||x_i−y_i||+e_{α_i} proves both independence of representatives and Lip(S_α)≤1. The S_α commute exactly, coordinate by coordinate. C_U is bounded, nonempty, convex and norm closed. If X_U is reflexive, Source328's **already proved commuting corollary** applies to this entire family and to every invariant closed convex subset of C_U.

This condition is automatic for superreflexive X, in the original ultrapower norm: all finitely representable spaces are reflexive. No equivalent norm is substituted into nonexpansiveness. Thus the source plus Wiśnicki's actual proof already resolves the whole superreflexive existence case and its commuting-family version. That is a composition to credit, not a nominee.

The crucial original operation is stronger than obtaining an approximate fixed point. If ỹ is fixed by every S_α and ||ỹ−j(x₀)||<δ, then for every ε>0 there is x∈C with ||x−x₀||<δ and ||T^n x−x||<ε for **all sufficiently large n**. Otherwise choose representatives y_i in that δ-ball and inductively select α_i increasing with ||T^{α_i}y_i−y_i||≥ε, contradicting S_α ỹ=ỹ. This diagonal selection must be included before naming a missing convergence step.

Subsequent work must carry the local correction construction, including all ball and invariance requirements, rather than stop at this observation.

## Completing the local correction construction

Here is a full version of the strongest compatible existence reduction, rather than just its initial ultrapower step. It is Wiśnicki's operation, with a convenient equivalent indexing set. Let D=diam(C)>0; the singleton case is immediate. Assume X_U is reflexive. Let A consist of **all** sequences α=(α_i) of positive integers tending to infinity, ordered coordinatewise. It is directed (take coordinatewise maxima). The maps S_α above are well-defined nonexpansive selfmaps and satisfy S_α S_β=S_{α+β}. There is no monotonicity requirement on α_i in this formulation. This avoids having to assert, without proof, that subtraction of two increasing sequences is increasing.

For fixed β∈A, translation α↦α+β identifies the tail {α≥γ} exactly with {δ≥γ+β}: δ−β≥γ implies δ−β∈A. Thus for **any** bounded scalar function h on A,

    limsup_α h(α+β) = limsup_α h(α).

The upper limits are the directed-net infimum of tail suprema. This equality, not just an unspecified appeal to cofinality, is the invariance calculation needed below.

Fix q∈(0,1). The common fixed point provided by Source328 in C_U and the diagonal lemma give x₁∈C with

    ||T^n x₁−x₁|| < D q   for every n≥N₁.

For example, apply the lemma with any center x₀∈C and radius 2D, which contains all representatives after adjustment on a U-small set. Suppose x_j is constructed with all sufficiently late displacements <Dq^j. Write ε_j=Dq^j, and define, for y∈C_U,

    r_j(y) = limsup_{α∈A} ||S_α j(x_j)−y||,
    K_j = {y∈C_U:r_j(y)≤ε_j}.

These sets meet every source hypothesis:

1. **Nonempty:** j(x_j)∈K_j. For each α the defining late-displacement estimate applies on a U-large set, so ||S_α j(x_j)−j(x_j)||≤ε_j.
2. **Convex and norm closed:** r_j is 1-Lipschitz. Convexity follows from the triangle inequality and a common upper tail for the two centers; hence its sublevel is convex and norm closed. Norm-closed convex sets are weakly closed, so K_j is weakly compact in the reflexive X_U.
3. **Invariant under every S_β:** translation of the indexing tails and nonexpansiveness give

       r_j(S_β y)
       = limsup_α ||S_{α+β}j(x_j)−S_βy||
       ≤ limsup_α ||S_α j(x_j)−y|| = r_j(y).

4. **Locality:** for each α,

       ||y−j(x_j)|| ≤ ||y−S_αj(x_j)|| + ||S_αj(x_j)−j(x_j)||.

   Taking the upper limit gives ||y−j(x_j)||≤2ε_j on K_j.

Source328's commuting corollary on K_j now supplies y_j fixed by every S_α. The diagonal lemma with δ=3ε_j and target tolerance ε_{j+1} produces x_{j+1}∈C with

    ||x_{j+1}−x_j|| < 3Dq^j,
    ||T^n x_{j+1}−x_{j+1}|| < Dq^{j+1} for n≥N_{j+1}.

Consequently x_j converges in norm to x∞∈C and

    ||x∞−x_j|| ≤ 3D q^j/(1−q).

For n≥N_j, the intermediate-sense inequality yields

    ||T^n x∞−x∞|| ≤ e_n + 2||x∞−x_j|| + Dq^j.

First n→∞, then j→∞, proves T^n x∞→x∞ in norm. Norm continuity of T then gives Tx∞=x∞ by comparing T(T^n x∞) with T^{n+1}x∞. **The original orbit of an arbitrary initial point is not asserted to converge.** The sequence x_j uses repeated compactness choices, not a prescribed implementable iteration.

A norm-closedness detail for C_U: if z∈X_U is in the norm closure of C_U, then lim_U dist(z_i,C)=0 for a bounded representative (z_i). Choose c_i∈C with ||z_i−c_i||≤dist(z_i,C)+1/i. Then [(c_i)]=z. This proves C_U is norm closed without assuming coordinatewise convergence.

A finite-representability detail for applying the pin in the original norm: for a finite-dimensional subspace E⊂X_U, choose representatives of a basis and the induced coordinate maps L_i:E→X. Their norms have a common finite bound. Choose a finite fine net in the unit sphere of E. The equalities lim_U||L_i v||=||v|| at those finitely many net points hold simultaneously on a U-large set. The uniform operator bound extends the inequalities to the whole sphere. Hence some L_i is an arbitrarily close linear isometry on E. Thus X_U is finitely representable in X; superreflexivity makes X_U reflexive. No renorming changes T or S_α.

### A quantitative-looking corollary already contained in this reduction

Let r(x)=limsup_n||T^n x−x||. The same construction bounds

    dist(x,Fix(T)) ≤ 2 r(x)

whenever X_U is reflexive. To see the exact constant, take ε>r(x), form K={y:limsup_α||S_αj(x)−y||≤ε}; then K contains j(x), is invariant and lies in B(j(x),2ε). A common fixed y∈K and the diagonal lemma produce an arbitrarily tail-accurate x₁ at distance <2ε+η from x. Choose its tail displacement arbitrarily small, and run the geometric correction above. Its total subsequent displacement can be made <η. Hence dist(x,Fix(T))≤2ε+2η; let ε↓r(x) and η↓0. Attainment of the distance is not asserted.

This bound is a direct refinement of the primary correction argument; it is **not** isolated as a new contribution. It supplies no uniform bound on N_j, no effective compactness modulus, and no convergence rate for a fixed numerical algorithm.

### The already available family extension

For a commuting family {T_t}, let v be a finite list of distinct parameters with positive integer exponents and let A_v be the corresponding product. Define its additive expansion

    a(v)=sup_{x,y∈C}(||A_vx−A_vy||−||x−y||)≥0.

Commutativity and the triangle inequality imply a(v+w)≤a(v)+a(w). Every sequence v_i with a(v_i)→0 defines a nonexpansive lift [(x_i)]↦[(A_{v_i}x_i)]. All such lifts commute. Wiśnicki's Theorem 3.3 applies the same common-fixed-point and local-correction mechanism to this larger directed system, with products selected by the bound a(v)≤1/(n+1). It corrects simultaneously for all products satisfying the threshold, so it already gives common fixed points for an arbitrary, potentially uncountable family. Merely replacing a single T by such a family would duplicate the primary result. Theorem 3.3 does **not** claim a nonexpansive retract, and its closing Remark identifies the separate orbit-limit requirement used in the 2001 retraction theorem.

## A concrete obstruction to dropping ultrapower reflexivity

This is an explicit calculation, not a conjectural objection to the stipulated source. Put

    X = ( ⊕_{n≥1} ℓ¹_n )_{ℓ²}.

Its dual is (⊕_{n≥1}ℓ∞_n)_{ℓ²}, by coordinatewise duality and Cauchy–Schwarz, and its bidual is (⊕_{n≥1}ℓ¹_n)_{ℓ²}. The canonical map is onto; X is real reflexive. This also follows directly by applying the finite-dimensional duality in each block and the ℓ² tail estimate. Completeness is inherited from the ℓ² sum of complete finite-dimensional blocks.

Let U be a free ultrafilter on N. For a=(a_k)∈ℓ¹, let z_n(a)∈X be supported only in block n, where its coordinates are (a₁,…,a_n). Define J(a)=[(z_n(a))]∈X_U. Then J is linear, and

    ||J(a)|| = lim_U ∑_{k≤n}|a_k| = ||a||₁.

Thus X_U contains an isometric closed copy of ℓ¹ and cannot be reflexive. More concretely, the set

    Δ={a∈ℓ¹:a_k≥0 and ∑_k a_k=1}

is nonempty, norm closed, convex and bounded, and the right shift σ(a)=(0,a₁,a₂,…) is an isometry Δ→Δ without a fixed point: fixedness forces every coordinate to vanish. Transporting Δ and σ by J exhibits an actual failure of the general FPP inside X_U. Therefore the statement “every ultrapower of a reflexive X has the property needed for Bruck” is not merely unproved; it is false for this explicit X.

This does **not** exhibit a fixed-point-free asymptotically nonexpansive map on X. It only blocks applying Source328 indiscriminately to the lifted ambient space. A successful general-reflexive extension would have to use additional structure of the particular lifted C and family, or a different construction. Closed bounded convex subsets of X itself still have the stipulated FPP.

## Attempt to descend the lift, and the exact lost algebra

For real reflexive X there is a canonical contractive linear weak-limit projection

    Q:X_U→X,    Q[(z_i)]=w-lim_U z_i.

Well-definedness follows because a norm-U-null change has zero limit against every functional. Linearity follows from linearity of each evaluation. Weak lower semicontinuity gives ||Qz||≤||z||, and Qj=id_X. For C as above, Q(C_U)⊂C by weak closedness. Therefore each compression f_α=Q S_α j is a nonexpansive selfmap of C and Source328 applies to it. The step **Q S_α S_β j = Q S_α j Q S_β j** has no justification, and it can fail by a fixed amount even when T itself is nonexpansive.

Take E=R⊕∞ℓ² with ||(t,x)||=max(|t|,||x||₂), C=[0,1]×B_{ℓ²}, and let V be the unilateral right shift on ℓ². Set

    T(t,x)=(||x||₂,Vx).

The norm inequality | ||x||−||y|| |≤||x−y|| and the isometry of V give Lip(T)≤1. C is nonempty closed bounded convex, E is reflexive (indeed isomorphic to a Hilbert space), and T is norm continuous. For every n≥1,

    T^n(t,x)=(||x||₂,V^n x).

For fixed x, V^n x⇀0: test against an arbitrary y∈ℓ² and approximate y by finite support. Hence every diverging lift compression is the same map

    f_α(t,x)=f(t,x)=(||x||₂,0).

But f∘f=0, whereas f_{α+β}=f. At (0,e₁), the discrepancy has norm 1. Thus the compressed maps do not preserve the semigroup product even though the lifts commute and compose exactly.

There is also direct failure of factorization through Q. Let z=[((0,e_i))]. Then Qz=(0,0). For any α_i→∞,

    Q S_α z=(1,0),       f_α(Qz)=(0,0).

The first equality uses S_αz=[((1,e_{i+α_i}))]. Passing through Q loses the norm of the weakly null sequence. Adding weak continuity of T would repair some limit interchanges, but is not a consequence of the current assumptions and would change the research target.

This example does not refute the desired asymptotic fixed-point theorem: T itself has fixed point (0,0). It does prove that the specific compression argument is insufficient. Taking convex combinations of compressed maps restores the finite-tuple approximation available in the source, but it cannot restore an algebra identity already false for the individual compressed generators.

## What the strongest retraction construction really needs

The Domínguez Benavides–Lorenzo Ramírez 2001 manuscript defines property (ω) for D⊂C by requiring every weak subsequential limit of {T^n x} to belong to D whenever x∈D. Its (ω)-FPP requires a fixed point of T in **every** nonempty norm-closed convex such D. Ordinary hereditary FPP, as supplied by Source328, only applies to an actual nonexpansive selfmap of an invariant D; D having property (ω) does not give T(D)⊂D.

Their Theorem 2 actually constructs an ergodic nonexpansive retraction under (ω)-FPP even for the weaker pairwise condition limsup_n||T^n x−T^n y||≤||x−y||. Here is the paid mechanism:

* Cesàro maps A_n=(I+T+⋯+T^{n−1})/n have ||A_nTx−A_nx||≤diam(C)/n. Their pointwise weak cluster maps are nonexpansive, preserve all norm-closed convex T-invariant subsets, and satisfy fT=f. The last equality evaluates f at the fixed arguments Tx and x, so does not pass T through a weak limit.
* Let N be the compact convex semigroup of all such nonexpansive maps. The initial Cesàro cluster proves N≠∅. Every f∈N fixes Fix(T), since invariant singleton sets must be preserved.
* Choose a minimal element R for the family of pairwise distances ||Rx−Ry||. For any h∈N, hR∈N and nonexpansiveness gives pairwise domination; minimality forces equality on every pair.
* For fixed x, K_x={f(Rx):f∈N} is nonempty weakly compact convex. If y=f(Rx) and T^{n_k}y⇀z, take a pointwise weak subnet limit s of T^{n_k}. Pairwise asymptotic nonexpansiveness makes s nonexpansive, and sf∈N. Thus z∈K_x. So K_x has property (ω).
* (ω)-FPP now supplies h∈N with y=h(Rx)∈Fix(T). For this y, hRy=y. Minimality gives

      ||Rx−Ry||=||hRx−hRy||=0.

  Since Ry=y, Rx∈Fix(T). Therefore R is a nonexpansive retraction, RT=R, and R preserves all closed convex T-invariant sets.

One can implement the minimality step with closed distance-dominating sets in the compact N, or use the correction explained in Bruck 1975 to his earlier strict-order initial-segment argument. It does not require strict convexity here. The actual unpaid assertion is obtaining (ω)-FPP under the contemplated reflexive/asymptotic hypotheses, not construction of the retraction once it holds.

There is a stronger finite-family operation to credit as well. For commuting asymptotically nonexpansive T₁,…,T_n, suppose the known retraction theorem has supplied a nonexpansive R onto

    F = ⋂_{i=2}^n Fix(T₁T_i).

F is T₁-invariant. Although T₁ need not be nonexpansive, on this range

    T₁R = T₁^{k+1} T₂^k R.

Therefore Lip(T₁R)≤Lip(T₁^{k+1})Lip(T₂^k)→1. Taking the infimum over k proves T₁R **exactly** nonexpansive. Its fixed points are precisely ⋂_{i=1}^n Fix(T_i). Source328 can then be applied to T₁R, with Bruck's retraction machinery for its fixed set. The original 2001 Theorem 4 completes the infinite-family step by directed intersections. It would be inaccurate to call nonexpansiveness of T₁R, or the finite-to-infinite family step, a missing operation after these primary proofs have been credited.

For intermediate-sense maps the same displayed identity, when F is available, gives an additive estimate

    ||T₁Rx−T₁Ry||≤||x−y||+e_{1,k+1}+e_{2,k},

so again its limit is nonexpansive. This small extension of the estimate is routine; it does not supply the missing retractions onto product fixed sets.

Finally, their Proposition 1 already gives the exact estimate

    ||T^n x−Rx||≤2 dist(T^n x,Fix(T))

when R is a nonexpansive retraction satisfying RT=R. Indeed choose p∈Fix(T) arbitrarily close to T^n x and use ||Rx−p||=||RT^n x−Rp||≤||T^n x−p||. Under an additional error bound ||z−Tz||≥c dist(z,Fix(T)), this becomes

    ||T^n x−Rx||≤(2/c)||T^n x−T^{n+1}x||.

The error-bound constant c and a displacement rate must be separately supplied. This familiar composition is not a new quantitative discovery.

## Trying the source anchor directly with asymptotic resolvents

The previous failure of ultrapower compression does not by itself rule out adapting the actual source. The following calculations push that alternative to its concrete missing inputs. They are prefreeze feasibility work, not a theorem announcement.

Assume now the **stronger Lipschitz** asymptotic condition Lip(T^n)≤L_n=1+ε_n with ε_n≥0 and ε_n→0. Let L₀=1 and keep all early L_n finite. Fix n and t∈(0,1) with (1−t)L_n<1. The contraction mapping u↦ta+(1−t)T^n u on C has a unique fixed point Q_{n,t}(a). Direct subtraction gives

    Lip(Q_{n,t}) ≤ t/[1−(1−t)L_n]
                   = 1/[1−(1−t)ε_n/t].                         (A)

Its displacement relative to the **n-th iterate** obeys

    ||T^n Q_{n,t}(a)−Q_{n,t}(a)|| ≤ tD.                       (B)

The same computation against a yields

    ||Q_{n,t}(a)−a||
       ≤ [(1−t)/(1−(1−t)L_n)] ||T^n a−a||
       ≤ c_{n,t} ||Ta−a||,

    c_{n,t}=[(1−t)/(1−(1−t)L_n)] ∑_{j=0}^{n−1}L_j.          (C)

The last inequality telescopes T^n a−a and uses
||T^{j+1}a−T^j a||≤L_j||Ta−a||. No commutation of T with a convex combination was used.

Choose t_n=max(√ε_n,1/n) for sufficiently large n so that t_n<1. This tends to zero and ensures the contraction inequality. If θ_n=(1−t_n)ε_n/t_n, then 0≤θ_n≤√ε_n<1, and (A) gives

    Lip(Q_n)−1 ≤ √ε_n/(1−√ε_n).

Thus one really obtains maps with asymptotically unit Lipschitz constants and vanishing n-th-iterate defects; their finite displacement constants (C) are explicit. If G₁,G₂ have displacement constants c₁,c₂ relative to ||Ta−a|| and G₁ is L-Lipschitz, their composition has displacement constant Lc₂+c₁. Pointwise convex combinations have the convex combination of the displacement constants. These calculations recover a perturbed version of the source's map algebra, rather than simply declaring its resolvents unavailable.

What (B) does **not** supply is a small defect for T itself. Let

    a_n = sup_{z∈C}||T^{n+1}z−T^n z||.

For u=Q_n(a), the exact estimate is

    ||Tu−u|| ≤ (L₁+1)t_nD + a_n.                            (D)

Indeed insert T^{n+1}u and T^n u, use the Lipschitz bound L₁ on T and (B). Uniform asymptotic regularity a_n→0 would therefore give the source-style uniform small T-defect. It is a genuine extra hypothesis. For example on C=[−1,1], T(s)=−s is nonexpansive and every even T^n is the identity. For even n the resolvent Q_{n,t}(a)=a has zero T^n-defect for **every** t, yet at a=1 its T-defect is 2. In this example a_n=2=diam(C), so (D) accurately exposes the missing term.

Even with a_n→0, (A)–(D) alone do not prove a new theorem: they give nearly nonexpansive maps and approximate fixed points, not the source's diameter-one compact detector on a common domain. The original Goebel–Karlovitz step explicitly used exact T-invariance of a minimal convex K and r(Tz)≤r(z), s(Tz)≤s(z). Replacing T by T^n only gives r(T^n z)≤L_n r(z), and T^n need not preserve the proposed minimal orbit-limit set at each finite time.

Here is what **can** be recovered with no suppressed invariance assumption. For a reflexive X and norm-continuous T as above, consider all nonempty norm-closed convex D⊂C having property (ω). Decreasing chains have a nonempty weakly compact intersection, and the property is preserved because an orbit starting in the intersection has all its weak limit points in every member. Thus Zorn supplies a minimal such D. For any approximate fixed point sequence (u_j) in C, put on all of X

    r(z)=limsup_j||u_j−z||.

The function r is convex and 1-Lipschitz, hence weakly lower semicontinuous. For each fixed m, (C)'s telescoping estimate gives ||T^m u_j−u_j||→0, and so

    r(T^m z) ≤ L_m r(z),        z∈C.

If w∈ω_T(z), choose m_k→∞ with T^{m_k}z⇀w; weak lower semicontinuity gives r(w)≤r(z). Therefore every nonempty sublevel of r in D is again a closed convex set with property (ω). Minimality forces r to be **constant on D**.

This is a real part of the diametral reduction, but it does not pay its whole cost. If additionally u_j∈D, a weak cluster a∈D and constancy r=R give ||z−a||≤R for every z∈D. Thus

    diam(D) ≤ 2R.

The source needs R=diam(D), not only this factor-two estimate, to get detectors approaching 1 against all prescribed test points. We have not proved constancy of s_D(z)=sup_{w∈D}||z−w|| on D, nor a norm selection of approximate fixed points **inside D** from mere orbit-limit invariance. The high iterates and Q_n take values in C, and weak limit inclusion in D does not imply norm distance to D tends to zero. Those are explicit missing obligations in this direct anchor route. No hypothetical “the same tree proof works” is adopted.

If the diameter-one detector and the necessary same-domain map algebra were proved, one would still have to redo the source's tree sensitivity and weighted switching with the precise products of (A)'s Lipschitz constants. Summably small excesses are a plausible error budget, but without the earlier geometric input a completed finite-witness inequality cannot be claimed. There is no frozen theorem for this route.

## Topological and quantitative boundary checks

The elementary map

    P(t,x)=(||x||₂,x) on [0,1]×B_{ℓ²}⊂R⊕∞ℓ²

is nonexpansive and idempotent. Its fixed set is the graph t=||x||₂. This is norm closed but nonconvex: (1,e₁) and (1,−e₁) are fixed, while (1,0) is not. It is not weakly closed either: (1,e_n)⇀(1,0), with every (1,e_n) fixed. Thus neither convexity nor weak closedness of a general nonexpansive fixed set can be inserted into a transfer. It also shows that the general demiclosedness implication x_n⇀x, ||Tx_n−x_n||→0 ⇒ Tx=x fails even for exact fixed sequences in a real reflexive space with the original max norm. This does not conflict with the existence and retraction conclusions of Source328.

Existence by itself gives no norm convergence of the Picard iterates: T(s)=−s on [−1,1] has a fixed point, but the orbit of 1 alternates. For a fixed averaging parameter λ∈(0,1), the averaged iterates of T_a(s)=(1−a)s on [0,1] starting at 1 are (1−λa)^n, with unique fixed point 0. For every prescribed n and every tolerance ε∈(0,1), choose 0<a<(1−ε^{1/n})/λ (and a<1) to keep that iterate above ε. Thus no uniform distance-to-fixed-point convergence rate depending only on the domain diameter and λ follows over this class. This statement concerns distance to fixed points, **not** residual rates for Krasnosel'skii–Mann iteration, which are a different question.

For a complex Banach space, realification keeps the norm, convexity over real scalars, boundedness, norm closedness and the selfmap inequality. Reflexivity is preserved. Any application to this unchanged assertion therefore gives a routine realification consequence; complex linearity of T is neither assumed nor inferred. No separate complex result is nominated.

## Research disposition at the end of the mathematical work

PREFREEZE / no nominee. No exact theorem was frozen and then weakened. No statement from an excluded closed round was read, renamed or offered for a new grade. The developed family is only Source328.

The completed mathematical content is the integrated superreflexive ultrapower/local-correction construction; the product/retraction reduction conditional on the actual orbit-limit fixed point property; explicit failure of general ultrapower reflexivity and of weak compression algebra; and the near-resolvent and minimal orbit-limit-set calculations above. These do not close a distinct full-scope consequence after the paid constructions. The unrestricted reflexive asymptotic case remains unproved here. So does orbit-limit FPP under the contemplated general hypotheses. The missing obligations are described by the displayed inequalities and sets, not asserted to be impossible.

No correctness, contribution, acceptance or count is assigned. No worldwide-priority claim or exhaustive literature/history clearance is made. Additional assumptions such as uniform convexity, normal structure, GGLD, strict convexity, weak continuity, uniform asymptotic regularity, or a metric error bound are never silently supplied.
