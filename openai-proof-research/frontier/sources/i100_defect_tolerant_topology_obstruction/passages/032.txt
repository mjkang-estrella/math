# I97 — original-proof audit and sharp relative involution stabilization

**Original I94 A: ORIGINAL PASS WITHOUT REPAIRS. Original I94 B: ORIGINAL PASS WITHOUT REPAIRS. R94: unproved and unrefuted. No substantial nomination; accepted count remains eight.**

This is an independent AI review of the original I94 proofs and an author investigation of their remaining sharp construction problem. These are separate decisions. The new technical results below constrain the geometry of a possible solution and locate the precise defect in a quotient-first obstruction argument. They do not determine the threshold. No human peer review, formal certification, or worldwide priority is claimed.

All pinned OpenAI theorems **and their lower proof operations** are premises at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. No upstream theorem is challenged, and no inconsistency between premises is used to derive a result. Applications of an accepted nonfilling theorem to a hypothetical additional embedding are ordinary conditional obstructions, not ex-falso synthesis. Only the three assigned I97 paths are written. No children, shared-ledger changes, staging, commits, or pushes were used. No I95/I96 artifact is an input.

## 1. The actual object and the original-proof decisions

Let **N** denote the pinned October 4 manuscript *Nonhomeomorphic closed aspherical four-manifolds with the same homotopy type*, **PD** the September 24 PD4 manuscript, **MT** the September 24 marked-tensor disk-embedding manuscript, and **BO** its boundary-only companion. Exact originals, Git identities, read ranges, and passage hashes are bound by the evidence package. Source references here mean those originals, not catalogue statements.

Use N's full construction with `m_R=m_B=5`, `p=9`. Write `b` for the number called `k` in N's `chambers.tex`. Ten ports of each color give `(10·9)^2=8100` ordered distinct `(R,B,R,B)` tuples, each with `(p+1)^4` independent conjugator choices and `2^4` signs. Thus

\[
b=129600(p+1)^4=1,296,000,000,\qquad r=\operatorname{rank}H=10+p+b.
\]

Let `w:H→Z` send every plumbing generator `τ_r` to one, and every extra generator `l_s` and bottom normal-circle generator `z_j` to zero. Put `H_d=w^{-1}(dZ)`. The boundary map `π₁S→H` is the actual marked surjection. The smooth chamber `D` has homotopy type `BH∨∨^{2b}S²` and full framed hyperbolic equivariant middle form. Attaching its specified three-cells gives the oriented PD4 pair `(P,S)` with `P≃BH`.

The actual `V=D'_2` is obtained using **all** source bodies and N's red-at-0/blue-at-1 cap selection. The `2b` embedded hyperbolic pairs have disjoint punctured-product neighborhoods `N_j`. Replacing all of them with balls gives `V` and the prescribed relative equivalence `(V,S₂)→(P₂,S₂)`, identity on the boundary. Consequently

\[
(D_2,S_2)\cong (V\#2b(S^2\times S^2),S_2)
\tag{1}
\]

in oriented TOP, with the original fundamental-group and boundary markings. The ball identifications extend over balls in TOP. This is reversal of the actual geometric replacement, not classification from an intersection form. Let `θ` be the specified nonidentity boundary deck transformation. All sums below are interior and all relative homeomorphisms fix `S₂` pointwise.

**Defects and repairs in ORIGINAL A: none found; none made. Defects and repairs in ORIGINAL B: none found; none made.** The following expanded checks explain steps already present in the original proofs; none changes their hypotheses or fills a missing mathematical premise. The discovery refinements in §§3–5 are not used retroactively to pass A or B.

### A: unrestricted-order relative nonextension

The original statement quantifies over every compact connected oriented TOP graph-type marked filling `W` of `S₂`, and excludes every homeomorphism with boundary restriction exactly `θ`. It imposes no order condition. The following interfaces pass.

1. **Exact lift.** Put `γ=τ₁`, `K=ker w`. The marking identifies `π₁W=H₂`, and `π₁S₂→H₂` is onto. Thus `∂\widetilde W` is connected. Its map to `S` is precisely the regular boundary cover with deck group `H`, obtained by quotienting `π₁S` by the marking kernel. A lift of the boundary map `θ` is the prescribed action of `γ` on this cover. Choose a lift `u` of `h` having that value at one boundary point. Connectedness makes its whole boundary restriction that lift. Comparing restrictions of deck transformations, which act faithfully on this connected boundary cover, gives `ugu^{-1}=γgγ^{-1}` for every `g∈H₂`. This is stronger than merely choosing a representative of an outer automorphism.
2. **Descent and commutation.** Conjugation by `γ` preserves `K`; hence `u` descends to `h'` on `X=K\backslash\widetilde W`. The deck generator `T` corresponds to `γ²`; since `Ad_γ(γ²)=γ²`, `h'T=Th'`. On `∂X=S_∞`, `h'` is exactly one-step translation. No equality `u²=γ²` is needed for A.
3. **Proper height.** A map representing `w/2` lifts to `t:X→R` with `t(Tx)=t(x)+1`. A compact set `C` with `\bigcup T^jC=X` exists by compactness of `W`. If `t(C)⊂[a,b]`, then `t^{-1}([A,B])` lies in the finite union of `T^jC` for `A-b≤j≤B-a` and is closed therein. This proves properness; no properness of an arbitrarily chosen classifying map is assumed.
4. **Free proper cocompact quotient.** The height displacement of `h'` is `T`-invariant and bounded by `c`. For an integer `q>c+1`, `F=T^qh'` has increments between `q-c>0` and `q+c`. Both positive and negative iterates escape every bounded height band. This proves freeness and proper discontinuity, including the compact-set criterion. The first nonnegative height in each orbit belongs to `[0,q+c]`, so a compact band meets every orbit. The quotient `Y=X/⟨F⟩` is a compact TOP manifold with collared boundary. Boundary orientation forces `h`, and therefore `F`, to preserve orientation.
5. **Group and boundary marking.** The lift `γ^{2q}u` generates the quotient deck group over `K`, with conjugation `Ad_{γ^{2q+1}}`. Since the quotient is infinite cyclic, no extra relation is introduced: the group is `K⋊Z≅H_{2q+1}`, fixing `K` and sending the stable letter to `γ^{2q+1}`. On the boundary this is the very same group action, so `∂Y` is the **identified** `S_{2q+1}` with its original marking, not an abstractly homeomorphic boundary.
6. **Graph type and relative equivalence.** `\widetilde W` is contractible because `W≃BH₂`. It remains the universal cover of `Y`; hence `Y≃BH_{2q+1}`. Classification of maps to a `K(H_{2q+1},1)` gives the prescribed boundary marking up to homotopy. The boundary collar's homotopy extension property changes the comparison with `P_{2q+1}` to the identity on `S_{2q+1}`. This is exactly N's marked-filling interface. For `2q+1≥3`, N's odd nonfilling theorem applies.

This is N's complete cyclic-height operation with the boundary lift retained. The original A is correct and technical under the stipulated lower-operation premise.

### B: the even-tail spectrum

Write `W_k=V#k(S²×S²)` and let `Σ(V,θ)` be the stabilization numbers admitting a free orientation-preserving TOP involution restricting exactly to `θ`.

The upper bound `2b∈Σ` follows from (1) and the actual deck action. The `+2` operation removes two small balls exchanged by an existing involution, attaches two punctured products by matched boundary maps, and exchanges the added pieces using mutually inverse identifications. Thus the map still squares to the identity, is free, and retains exactly the boundary map. There is no hidden unrestricted-order extension in this step.

For a hypothetical involution on `W_k`, let `Z=W_k/C₂`. Its boundary is the identified `S`. The diagram of boundary/interior covering sequences is essential: if `N_S=ker(π₁S→H)`, then the kernel of `π₁S₂→π₁W_k` is also `N_S`, viewed in the index-two subgroup. The map `π₁S→π₁Z` is onto because it surjects onto the parity quotient and its even subgroup surjects onto `H₂`. An element in its kernel is even and is in `N_S`; conversely every element of `N_S` dies upstairs. Therefore `π₁Z=H` **with the prescribed boundary map**. No arbitrary extension of `H₂` by `C₂` is substituted.

Duality for `(P,S)` gives `H₂(P,S;Z)=H₁(P,S;Z)=0`, and hence `H₁(S;Z)→H₁(P;Z)` is an isomorphism. The exact marking transfers this isomorphism to `Z`. Rational transfer gives `H₃(Z;Q)=0` from `H₃(W_k;Q)=0`; nonempty boundary gives `H₄(Z;Q)=0`. Finite-CW homotopy type and Euler characteristic of a cover give

\[
\chi(W_k)=2-2r+2k,\quad \chi(Z)=1-r+k,\quad b_2(Z)=k.
\]

The boundary `H₁` isomorphism and Poincaré–Lefschetz duality make `H₂(Z;Q)→H₂(Z,S;Q)` onto between equal finite dimensions, hence an isomorphism. The rational middle form is nonsingular. This checks the often-missed distinction between an arbitrary form on absolute homology of a manifold with boundary and the nonsingular form used for parity.

The original proof **does not multiply the signatures of manifolds with boundary**. It glues `C=Z∪_S(-D)` and `\widetilde C=W_k∪_{S₂}(-D₂)` along their entire marked boundaries. Their boundary covers match exactly, so `\widetilde C→C` is a closed oriented double cover. N's free graph-and-sphere model identifies the ordinary forms of `D,D₂` with augmented hyperbolic forms; both signatures vanish, as does that of `W_k`. Whole-boundary Novikov additivity therefore gives `σ(\widetilde C)=0`, `σ(C)=σ(Z)`. The **closed TOP** finite-cover signature theorem gives `0=2σ(Z)`. The primary Ranicki text, Proposition 22.26 with 22.27, is applicable; its pp.269–270 boundary-defect comparison explicitly uses this closed gluing. The retained text has duplicate extraction layers; the recorded `str.splitlines()` ranges, not LF offsets, identify the propositions.

Rank `k` and signature zero of a nonsingular real symmetric form force `k` even. A excludes zero. Nonemptiness and `+2` closure then give exactly

\[
\Sigma(V,\theta)=\{2\kappa,2\kappa+2,\ldots\},\qquad 1\le\kappa\le b.
\tag{2}
\]

The original B is correct and technical. Neither the audit nor any result below changes the bound in (2).

## 2. Exact discovery question and paid interfaces

R94 asks for a free orientation-preserving TOP involution on the particular `(W₂,S₂)`, with restriction **equal** to `θ`. The quotient construction must yield the same relative homeomorphism type, not merely the same rank, homotopy type, or algebraic form. Conjugation by a boundary-fixed homeomorphism is allowed. An arbitrary automorphism of a free group, a diffeomorphism extending `θ` without order two, and an action after an unknown number of sums do not solve R94.

The two developed routes below have different unpaid steps. Route I now has a sufficient geometric complement criterion, complete group-label bookkeeping at the first Whitney stage, and a new restriction on what the residual two summands may look like equivariantly. Route II has integral/spin constraints and an exact cohomological defect budget for the source cut construction. None is promoted to a substantial theorem.

## 3. A technical obstruction to a geometrically split residual action

**Lemma C (no free orbit of punctured products at the sharp count).** Suppose `a` is a solution of R94. There is no locally flat interior codimension-zero embedding

\[
N\cong(S^2\times S^2)\setminus\operatorname{int}B^4\ \subset W_2
\]

with `N∩a(N)=∅`. Equivalently, its quotient `Z` contains no such punctured product. In particular its ordinary hyperbolic form, established below, cannot be realized by an embedded framed sphere pair meeting once.

**Proof.** The universal cover of `W₂` has reduced integral homology only in degree two, with free module `Λ⁴`, `Λ=ZH₂`, and standard hyperbolic form. This follows by reversing the actual source replacement and retaining just two product summands. Assume `N,aN` are disjoint. Their four factor spheres have a standard nonsingular block-diagonal pairing over `Λ`: an embedded simply connected product has no nonidentity self-translate intersections. After whiskers are fixed, let `A` be their square class matrix in the standard module and let `Q,J` denote the ambient and their hyperbolic matrices. Then

\[
A^*QA=J,\qquad (J^{-1}A^*Q)A=I.
\]

The source's direct-finiteness argument for matrix rings over a residually finite free group applies verbatim. A left inverse becomes a right inverse in every finite quotient's complex regular representation; residual finiteness separates the finite supports of matrix entries. Thus `A` is invertible and these four spheres form the **entire** middle basis, not just an ordinary homology basis.

Remove `N∪aN` and cap their boundary spheres with balls. The complement is connected and its fundamental group remains `H₂`, by van Kampen across simply connected `S³` interfaces. The full-basis Mayer–Vietoris calculation in N's even-filling proof applies to the common universal lifted complement: its `H₂` is zero, its `H₃` consists precisely of the boundary-sphere classes, and capping kills these classes without creating `H₄`. The capped universal cover is simply connected and acyclic, hence contractible. The capped manifold is a marked graph-type filling of the same `S₂`.

The involution exchanges the two removed pieces and their boundary spheres. Extend it to exchange the two balls by any extension of one boundary homeomorphism, and use the inverse in the other direction. This is a free orientation-preserving involution and still restricts exactly to `θ`. Original A forbids it. This proves the first assertion. A punctured product in `Z` lifts to two disjoint copies, since it is simply connected, proving the equivalent quotient assertion. A framed geometric dual pair has such a regular neighborhood. ∎

This does **not** forbid `W₂` from having its ordinary two product summands—it does. It says that every one of their punctured-product neighborhoods must intersect its image under any putative solution. Nor does C show that every action admits a disjoint translate of some product. That last assertion would be a new, unpaid localization theorem and would refute R94; it is not available here.

This rules out a tempting strong version of Route I: cancel the other pairs while leaving a geometrically untouched free orbit of two standard product neighborhoods. It also rules out building Route II's rank-two quotient by attaching a standard geometric product to a graph-type remainder. The necessary residual middle homology cannot remain geometrically split in the quotient. These are restrictions on proof strategies, not a counterexample to R94. Their proof is a short application of A and N's full-basis replacement, so their contribution is **technical**.

## 4. Route I — paired Whitney cancellation in the actual double cover

### 4.1 An exact sufficient complement condition

Fix the **actual** source collection `\mathcal N={N_j:1≤j≤2b}` in `D₂`, and let `t` be its deck involution. It would suffice to construct a collection `\mathcal C` of `2b−2` disjoint embedded punctured products such that:

- `t` permutes `\mathcal C` in two-element orbits;
- there is a boundary-fixed oriented TOP homeomorphism of `D₂` carrying `\mathcal C` onto a subcollection of `\mathcal N` of that size.

**Conditional complement bridge.** Under these two hypotheses, replacing `\mathcal C` by balls gives a solution of R94. Indeed, the first supplies a free action on the capped complement using paired ball extensions. The second extends over those balls and identifies the result with the partial source replacement. The two unremoved source neighborhoods make that partial replacement exactly `V#2(S²×S²)` relative to the original boundary. This proves the bridge without a relative classification theorem. A boundary-fixed ambient isotopy of collections is one sufficient way to pay the second hypothesis; equality of based sphere classes is not.

The homeomorphism here is **not required to be equivariant**, nor to make the other two neighborhoods invariant as a collection. Requiring that extra condition would contradict C. This separates the real complement problem from an impossible requirement to keep the last orbit geometrically untouched.

### 4.2 The first Whitney stage, with labels retained

The source system `\mathcal N` uses red caps at vertex 0 and blue caps at vertex 1. Its image under `t` uses the opposite choices. Each system is separately embedded; the union has the transverse intersections in the actual product plumbing charts. The full ordered four-tip list includes every port choice with independent conjugators and signs. No list entry, bottom generator, or conjugator can be removed from the manifold.

There is nevertheless a paid first-order fact stronger than an augmentation calculation. For each source row of cap-sheet intersections involving a rim sphere, hold its outer parallel index `ε` and the opposing sheet fixed. The two inner cap sheets have coefficients `εη` and `−εη`. Their whiskered group labels are equal in the actual exterior group, hence also in `H₂`; the unused upper cap supplies the nullhomotopy. BO's explicit carrier model makes the point transparent: attaching the selected cap to the upper punctured torus leaves the unused tip generator, and adjoining the actual unused cap kills it. The comparison loop runs through the common stem, the two inner cap tracks, and a short interval on the opposing sheet. It bounds in that carrier **as a map**, allowed to cross other cap images. This operation keeps the outside conjugators; it does not kill a bottom meridian.

Thus these specified canceling pairs have nullhomotopic Whitney circles in the actual exterior. In the smooth source manifold one can choose immersed Whitney disks for them by general position, with embedded boundary collars. Local boundary twists correct their Whitney framings if necessary, at the expense of new disk–sheet intersections. This pays immersed, framed first-stage disks only. Their interiors need not avoid the spheres, other Whitney disks, unused caps, or their deck translates. No Whitney move eliminating an intersection is claimed at this stage. Intersections between arbitrary other sphere combinations require their own label pairing; the row calculation is not asserted to cover every crossing of an eventual complete cancellation system.

Here is a usable exact deck convention, rather than treating deck translation as a linear order-two permutation over the group ring. Take `γ=τ₁` and `a=γ²`. For another odd generator `τ`, put `x=τγ^{-1}`, `y=γτ`; for an even generator `e` (each `l_s,z_j`), put `x_e=e`, `y_e=γeγ^{-1}`. These, together with `a`, form a Schreier basis of `H₂`. With `α=Ad_γ`,

\[
\alpha(a)=a,\quad \alpha(x)=ya^{-1},\quad \alpha(y)=ax,
\qquad \alpha(x_e)=y_e,\quad \alpha(y_e)=ax_ea^{-1}.
\tag{3}
\]

In particular `α²=Ad_a`, not the identity on based labels. A translated row with label `h` has label `α(h)` after the corresponding whisker transport. Translating it twice conjugates by `a`. The two outer rows may have distinct words `h_+,h_-`, including differences involving `z_j`; they must not be identified. The finite diagnostics test (3) on words, and explicitly retain unequal outer-phase words. These formulae apply uniformly to every entry of the huge list without pretending to have drawn all of it.

### 4.3 Why an auxiliary orbit has not yet solved the geometry

An attempted construction uses one free orbit of auxiliary hyperbolic pairs as geometric duals for the Whitney disks. For an intersection with a sheet, tubing a Whitney disk into a parallel of a framed dual sphere can remove that intersection when an actual tube path and the relevant geometric dual are available. But such a tube changes the disk by a based class `±h[A]`, where `h` is its path label. The translated move changes it by `±α(h)t_*[A]`. Framing is tracked by the framed tube; it is not supplied by the vanishing of an ordinary intersection number.

The unresolved simultaneous problem is that the parallel auxiliary sheets intersect their duals, other tubes can use those duals, and the unused caps giving the nullhomotopies already cross the opposing selected sheets. Replacing every algebraically canceling row by a separate immersed disk does not furnish disjoint embedded disks or disjoint translates. In particular the nullhomotopy of a row is in the ambient exterior, not established in the complement of the entire protected configuration. PRT's proof of disk embedding explicitly manufactures geometric duals for Whitney disks in the appropriate complement before producing clean embedded disks. It does not allow those complement steps to be suppressed.

The count also matters. Starting with `D₂`, if one **adds** a fresh free orbit of products and then cancels `2b−2` pairs, four product summands remain by Euler characteristic. To end at two, one must cancel `2b` pairs after adding two, or use two **existing** pairs as auxiliaries without increasing the count. An existential stabilization argument does not pay either ledger. If the resulting action leaves a clean free orbit of auxiliary products, C forbids it at count two. Therefore a successful auxiliary construction must both control the canceling disks and allow its remaining middle geometry to interact with the action.

**Missing geometric lemma I97-I.** Produce the above `\mathcal C` on this `D₂`, with full whiskered labels and product framings, disjoint embedded Whitney data and deck translates throughout all surgeries, and an actual relative complement comparison as in §4.1 (or a different proved comparison of equal strength). If auxiliaries are added, account for their removal so exactly two sums remain. This is not proved. The first-stage immersed disks, exact label transport, conditional complement bridge, and C are retained as technical progress; they do not amount to a cancellation construction.

## 5. Route II — the quotient, its nonsplit form, and a defect budget

### 5.1 Exact quotient equivalence and integral constraints

R94 is equivalent to constructing a compact connected oriented TOP manifold `Z` with boundary **identified** with `S`, a marking `π₁Z=H` restricting to the specified `π₁S→H`, and an oriented homeomorphism

\[
(Z_2,S_2)\cong(W_2,S_2)\quad\text{relative to }S_2,
\tag{4}
\]

where `Z₂` is the cover classified by `w mod 2`. Necessity is B's extension-group argument. Sufficiency is conjugation of the actual deck involution through (4), which preserves its order, freeness, orientation, and exact boundary action. The numbers `b₂(Z)=2`, `σ(Z)=0` are consequences, not replacements for (4).

**Lemma D (integral quotient form).** For every solution on `W_k`, its quotient has torsion-free `H₂(Z;Z)`, unimodular even ordinary intersection form of rank `k` and signature zero, and vanishing TOP `w₂`. In particular for `k=2` the integral form is `H`.

**Proof.** B already gives the marked `H₁(S;Z)≅H₁(Z;Z)≅Z^r`. The map `H₃(Z,S;Z)→H₂(S;Z)` is, under Poincaré–Lefschetz duality, the restriction `H¹(Z;Z)→H¹(S;Z)`, hence is an isomorphism. The pair sequence therefore makes `H₂(Z;Z)→H₂(Z,S;Z)` injective, and the `H₁` isomorphism makes it surjective. By duality and the universal coefficient theorem, `H₂(Z,S;Z)≅H²(Z;Z)≅Hom(H₂(Z;Z),Z)`, since `H₁Z` is free. Thus `H₂Z` is free and the integral intersection pairing is unimodular.

The graph filling `V` has `H²(V;F₂)=0`, so is spin; interior product sums are spin as well. Every sphere in `Z` lifts to `W_k`, so `w₂(Z)` evaluates to zero on every spherical class. The Hopf exact sequence and `H₂(H;Z)=0` show that spherical classes surject onto `H₂(Z;Z)`. Since `H₁Z` is free, they also generate `H₂(Z;F₂)`. Therefore `w₂(Z)=0`, and the Wu formula makes the ordinary integral form even. Rank and signature are B's already audited conclusions.

For completeness, an even rank-two form has matrix `[[2u,v],[v,2z]]`. Indefiniteness and unimodularity give `v²−4uz=1`. If `u=0`, there is an evident primitive isotropic vector. Otherwise `(v+1,−2u)`, divided by its gcd, is one. Unimodularity supplies a vector pairing one with it; subtracting half that vector's even square times the isotropic vector makes the second vector isotropic. The resulting basis has form `H`. This is a lattice calculation, not an embedding theorem. ∎

C and D together force a quotient with ordinary form `H` but **no geometric punctured-product summand**. That identifies why a naive quotient-first plan “realize the last algebraic plane geometrically and remove the rest” is too strong if it geometrically splits the final plane as well. We have not shown that the equivariant quotient form is the standard plane over `ZH`; its restriction to `ZH₂` is standard by (4). Descent of that form is a further algebraic constraint, not an available relative homeomorphism theorem.

### 5.2 Reusing the source cuts with the residual homology honestly retained

There is a quantitative bridge to N's odd-cycle argument, but it stops before a nonfilling theorem at positive rank.

**Lemma E (cut defect).** Assume a solution on `W_k`. For each odd `d≥3`, let `Z_d` be its marked degree-`d` cyclic cover. Attach the dual handles undoing all law surgeries, as in N's marked-cut operation, and call the resulting manifold `U_d`. The operation retains the law-cocore disks and prescribed outside faces. It yields connected vertex pieces and connected torus-boundary cuts over the same `Γ_d`. Over `C`, let `Δ^i:⊕_vH^i(V_v)→⊕_eH^i(Y_e)` be the differences of restrictions. Then

\[
\operatorname{coker}\Delta^2=0,\qquad
\dim\operatorname{coker}\Delta^1+\dim\ker\Delta^2=dk.
\tag{5}
\]

Moreover, at most `dim coker Δ¹` cuts can have degree-one boundary image different from both original meridian/longitude coordinate lines.

**Proof.** The double cover of `Z_d` is the degree-`d` cover of `W_k`. Lifting the actual connected-sum balls gives a graph-type cover of `V` with `dk` product sums, so its third rational homology vanishes and its second Betti number is `2dk`. Transfer gives `H³(Z_d;C)=0`. Euler characteristic and the Schreier rank `1+d(r−1)` give `b₂(Z_d)=dk`. The same marked boundary `H₁` isomorphism holds in every cover by duality for `(P_d,S_d)`.

The dual two-handles attach along the individually lifted free-factor generators `z_j`. On `H₁` their attaching classes are independent. The relative handle sequence thus leaves `H₂,H₃` unchanged, and kills exactly those free factors on `π₁`. Hence `H²(U_d;C)=C^{dk}`, `H³(U_d;C)=0`, and `π₁U_d` is the marked graph group of `X_d`.

N's proof of connected marked cuts, through its proof end, uses this fundamental-group marking, the prescribed boundary and cocore neighborhoods, and the contractibility of the tree fiber. It does **not** use `H²=0` until the subsequent linear-cut lemma. Its component-graph argument still applies: all named extra generators lie in principal pieces, so the component graph in the tree cover is a tree; discard closed cuts on finite hanging branches. The same punctured smoothing is used, with prescribed smooth handle/collar neighborhoods protected. Thus the cut construction itself is available here even though its graph-*homotopy*-type conclusion is not asserted.

The relevant Mayer–Vietoris segment is

\[
\bigoplus_vH^1(V_v)\xrightarrow{\Delta^1}\bigoplus_eH^1(Y_e)
\longrightarrow H^2(U_d)\longrightarrow
\bigoplus_vH^2(V_v)\xrightarrow{\Delta^2}\bigoplus_eH^2(Y_e)
\longrightarrow H^3(U_d)=0.
\]

Consequently there is a short exact sequence `0→coker Δ¹→H²(U_d)→ker Δ²→0`, proving (5). Each connected cut with one torus boundary has a one-dimensional boundary image `L_e` by half-lives/half-dies. If `L_e` is neither coordinate line, the restriction from either adjacent vertex piece vanishes on that torus: it lies in its own coordinate line, since that outside longitude bounds, and also in `L_e`. Projection from `⊕H¹(Y_e)` onto the direct sum of these anomalous `L_e` is onto and annihilates `im Δ¹`. It factors through `coker Δ¹`, proving the last bound. ∎

At the sharp count the budget is `2d`. This explicitly locates the failure of a proposed direct reuse of odd nonfilling. If `coker Δ¹≠0`, not all independent peripheral conditions or coordinate-line conclusions used by N are paid. Even if `Δ¹` is onto, (5) leaves a `2d`-dimensional kernel of `Δ²`; N's full-column vertex curvature-gradient minors used injectivity of the individual `H²` restrictions. That premise is now absent. One cannot erase this kernel and apply the endpoint-assignment theorem unchanged.

There is also a precise limit to just counting anomalous edges. The purely combinatorial odd cycle with five edges of each color per adjacency ceases to force N's deficient-color contradiction after **three** suitable edge deletions. Fewer than three deletions leave at least three edges of each color at every adjacency, forcing alternate deficient colors, impossible around an odd cycle. Conversely choose deficient colors alternating except on one closing adjacency, where both ends are deficient in red; delete three red edges there, assign one remaining red edge to each end, and assign every other edge toward a nondeficient endpoint. Each vertex receives at most one edge of its deficient color. This pays an endpoint assignment for the relaxed graph. The finite diagnostic checks the minimum over deficiency patterns and a triangle witness. It does **not** realize cuts, potentials, or a four-manifold. Since `2d≥6`, the defect bound alone cannot recover the original zero-defect combinatorial contradiction by this deletion test.

**Missing quotient lemma I97-II.** Construct `Z` with the actual marked boundary and (4), necessarily with D's form and C's absence of a geometric product summand; or prove an obstruction for such quotients that handles the residual cut defects in (5). No quantitative extension of the source tensor theorem controlling these defects is proved. No such quotient or relative-cover homeomorphism is constructed. Stable isometries, normal bordisms, and unspecified stable products do not supply (4).

## 6. Contribution audit and primary comparison

The full-domain exact searches are reproducible over 749 manuscripts and all 10,373 original blob positions, using the inherited I94 map of I14's 9,340 originals plus the 1,033 outside positions and all 776 inherited PDF text hashes. Three new searches have 576 geometric, 65 action, and 14 classification hits. These are **lexical searches, not a full semantic audit**. Exact line hits and complete selected-family inventories are retained. The four closest families are N, PD, MT, BO; every blob in those families is inventoried and the complete tree was checked for title variants. An additional surface-singularity family was inspected at its actual theorem: its holomorphic `μ`-constant hypotheses do not apply to these marked graph fillings. The broader inherited I94 screen remains evidence, not a claim to reread every companion proof.

The relevant lower operations were read through their ends: N's entire chamber, cyclic, model, and formal sections; PD's marked exterior/middle-form operation and entire marked stable-realization section; MT's marked-body, framing, and exterior-dual operations; BO's ribbon/stage and carrier-label operations. N's tensor theorem statement and complete odd-cycle corollary were read to identify the exact zero-defect input; its full tensor proof is not claimed independently re-audited. All these source results remain stipulated premises.

- **A and B:** the height, full-basis replacement, residual finiteness, boundary homology, and cyclic markings are already lower source operations. Closed signature transfer and orbitwise connected sum finish B. Their independent original-proof PASS does not make their contribution substantial.
- **C and §4.1:** combine A with the source's full-basis Mayer–Vietoris replacement and a relative homeomorphism of actual collections. C adds a useful necessary restriction to this project but is a technical application, not a substantial obstruction to R94 itself.
- **D and E:** integral duality, spherical generation for free groups, spin evaluation, and the exact cut sequence give the refinements. E keeps a rank previously set to zero in N's argument. It does not supply a new positive disk operation or a robust tensor nonfilling theorem.
- **MT/BO:** their product framings, unused-cap carriers and based cancellation pay the first immersed Whitney stage. They explicitly allow cap intersections. BO strengthens negative boundary control; it supplies no disjoint positive replacement for this problem. Accepting all those operations therefore does not silently solve the clean-complement or finite-order problem.
- **PD stable product:** it starts with a hypothetical closed aspherical model, makes a particular marked equivalence and an `s`-cobordism, and applies an existential stabilized product theorem. Its final periodic-lift operation preserves based classes, not a specified small relative stabilization or a descended involution. Every proof through the end of that section was read. Its hypotheses and count cannot be omitted.

The most relevant primary precedent is [Krushkal, *Surgery and involutions on 4-manifolds*, arXiv:math/0505394v2, published AGT 5 (2005), 1719–1732](https://arxiv.org/abs/math/0505394v2). The complete text through its proofs was inspected. Theorem 1.2 constructs double-cover graph-type fillings of canonical surgery boundaries; Corollary 1.3 distinguishes quotients from the additional `s`-cobordism identification needed for the **specific** filling. Its cap-selection construction is deliberately nonequivariant. Its fundamental-domain obstruction treats particular simple cuts, not the two-summand stabilization here. Thus the general involution reformulation and the need to identify the actual cover are classical; no priority is claimed for them. The new requested issue is the sharp count on N's fully marked example.

[Krushkal–Lee, arXiv:math/0103018v1, published 2002](https://arxiv.org/abs/math/0103018v1), was read in full, including both theorem proofs. Its free-group surgery result is for closed manifolds with intersection forms extended from the integers. Its boundary remark requires spherical boundary cuts; the source cuts here have torus boundary. Closing a chamber and using that result does not keep its separating marked `S` fixed or give (4).

[Powell–Ray–Teichner, published 2025](https://www.maths.gla.ac.uk/~mpowell/s00029-025-01069-y.pdf), Theorem A, Theorem 2.3 and their inspected proofs require a good fundamental group and retain geometric-dual information. They cannot be used as unrestricted free-group disk embedding. [Khan, published 2017](https://qkhan.pages.iu.edu/research/ARTICLES/CancellationTop4Mfld.pdf), Theorem 2.1 and Lemma 2.10, similarly use goodness in the actual re-splitting proof; its virtually abelian bound does not apply to `H`. [Auckly–Kim–Melvin–Ruberman, arXiv:1406.4937v2](https://arxiv.org/abs/1406.4937v2), Extension Lemma 2.3, requires actual disks and a specified handlebody complement, and explicitly distinguishes an extending automorphism from an involution. These are scope comparisons, not upstream audits.

The signature input is [Ranicki, *Algebraic L-theory and topological manifolds*](https://webhomes.maths.ed.ac.uk/~v1ranick/books/topman.pdf), Propositions 22.26–22.27 and the whole-boundary defect comparison. No relative signature multiplicativity theorem is imported.

## 7. Evidence replay, mathematical status, and exact handoff

The owned snapshots freeze the original I94 report and the repository instructions, pin, catalogue, complete tree, and four informational ledgers. Only the originals `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` may drift; their snapshots cannot. The original I94 seal and every file in its sealed inventory are immutable references. Its offline verifier is replayed unchanged, retaining the full original corpus identities, inherited searches and bounded PDF/render checks. No recursive corpus copy was made.

The I97 read manifest saves exact selected passages. All ranges are **one-based inclusive after UTF-8 decoding with `errors='replace'` and Python `str.splitlines()`**. A passage is hashed as the selected lines joined with LF and one final LF. Full-source SHA-256, total splitline count, and raw LF count are separately recorded. This matters for PDF form feeds and Ranicki's duplicate extraction layer. Tool-output truncations during broad reads were recovered by narrower reads before the final manifest; no truncated output is represented as a completed proof reading. New primary PDFs retain versioned URLs, final URLs and SHA-256 hashes. Krushkal v1 was downloaded first; v2 was then separately retained and is the version used for the full reading. The v1 artifact is download/hash evidence only. PDF text replay does not independently check every diagram.

The final verifier is offline and **READ-ONLY**. Run from the research root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B frontier/experiments/i97_relative_involution_stabilization/verify.py
```

It checks owned bytes and exact inventory, immutable references and input snapshots, the unchanged I94 seal and replay, every new search output, selected-family completeness, passage hashes and line conventions, all new primary PDF extractions, and the finite diagnostics. It performs no downloads, writes, bytecode generation, repairs, or resealing. All 776 inherited text hashes remain bound; no all-PDF re-extraction or full-corpus semantic audit is claimed. Finite diagnostics test Schreier word transport, phase-sensitive row cancellation, even unimodular binary-form reduction and the endpoint-deletion screen. They cannot produce Whitney disks, identify a relative complement, or prove novelty.

Preseal verification is run before creating the single final seal. Only that declared `seal.json` is excluded from the owned inventory. Failures and corrective steps, if any, are retained in the event record; no postseal edit is permitted. The seal hash is returned in the handoff rather than embedded circularly here.

**Independent original-proof review:** A and B both ORIGINAL PASS WITHOUT REPAIRS. **New mathematics:** author-level technical C/D/E, the conditional relative complement bridge, and first-stage immersed Whitney data; parent validation remains separate. **Discovery:** neither `κ=1` nor a larger threshold or general obstruction to `k=2` is established. **Contribution:** no substantial ninth finding. **Evidence:** a bounded mechanical replay verdict, independent of all those mathematical decisions; see the retained validation record and final read-only run.
