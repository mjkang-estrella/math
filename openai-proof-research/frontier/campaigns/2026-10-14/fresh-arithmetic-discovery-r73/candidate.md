# T253M73: the exact integral multiplier of the four-direction polygon group

**Author research submission, not an independent gate.** The frozen target is unchanged. The argument below purports to prove its full scope, relative to the stipulated pinned source operations and the explicitly cited classical inputs. Correctness and contribution require separate parent-owned review. No acceptance, count increment, worldwide novelty, or substantiality verdict is asserted.

## 1. Statement and contracts

Let tau=(1+sqrt(5))/2, O=Z[tau], and let a be **any** positive integer satisfying `eq:lambda-choice` in source253. Write lambda=tau^a. Use exactly the source's Stone space X, the four cuts with forms x, y, y-lambda*x, x-lambda*y at levels in O, and its groups F_m and A_m on m tracks. For **every finite m>=1**, the claim is

    H_2(A_m; Z) ≅ Z ⊕ (Z/2)^(M+9+2 epsilon),
    M = |Norm(1-lambda^2)| = L_a^2 - 2(-1)^a - 2,
    epsilon = 1 if 3 divides a, and 0 otherwise.

Here L_a is the Lucas number. This is an abstract integral abelian-group isomorphism, not a preferred basis. It does not assert type F_infinity, a torsion-free universal central extension, or any change in the number of tracks. There is no additional large-a or large-m threshold. The original freeze is `scope-T253M73.md`, SHA256 `b4725ee50cba2e070c471a5e444da16b563c52db96d45500759b270f48e747d5`.

Pinned source: **An Infinite Finitely Presented Simple Amenable Group**, source253, revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Exact URLs, Git blobs, and SHA256 values for the private reading copies are in `source-receipts.json`. We use its definitions, free minimal action Gamma=(O/Z)^2≅Z^2 on the Cantor space X, comparison lemma, simplicity theorem A_m=[F_m,F_m], corner module and square-induction operations, and explicit string resolution. Their truth is stipulated; this note does not audit them.

Classical inputs, with bounded reading disclosed in `reading-and-credit.md`:

* Xin Li, *Ample groupoids, topological full groups, algebraic K-theory spectra and infinite loop spaces*, [arXiv:2209.08087v2](https://arxiv.org/pdf/2209.08087v2), Lemma4.5, Theorem4.18, Theorems5.18–5.19, Corollary5.20, and Theorem6.12. These provide the bisection spectrum, its integral homology, the fixed-group transfer, and the low-degree Hurewicz edge map. These are credited operations.
* Franz Gähler, John Hunton, Johannes Kellendonk, *Integral cohomology of rational projection method patterns*, AGT13 (2013),1661–1708, [primary PDF](https://msp.org/agt/2013/13-3/agt-v13-n3-p12-p.pdf), particularly Theorem5.3 and its proof. Singular-stratum module sequences and exterior-power inclusion maps are classical here. The corner computation below is a concrete calculation within that method, not a claim to invent it.
* Inès Saihi, *Stable Homotopy Groups of Moore Spaces*, proceedings190 (2017),177–192, [arXiv:2408.15709v1](https://arxiv.org/pdf/2408.15709v1), Lemma2.4 and Theorem3.2 with proofs. The stable Moore-space extension and its doubling operation are credited. This PDF's scratch filename was initially misattributed to Strickland; the contents, final filename, and attribution have been corrected to Saihi.

The proof has two tasks beyond the source's finite-generation conclusion: a complete integral coefficient calculation, and an actual stable lift that removes the possible attaching-map obstruction. Integral coefficient homology by itself is insufficient.

## 2. Completing the corner module

Put H=O^2≅Z^4, R=Z[H], and let L be the source's group of compactly supported integer polygonal step functions on the plane, modulo changes on allowed line segments. Let V be the set of all intersections of nonparallel allowed lines. If r(z) directions occur at z, define

    Q_z = { (q_l)_(l through z) ∈ Z^r(z) : sum_l q_l=0 },
    Q = direct sum_(z∈V) Q_z,
    P = direct sum_(allowed lines l) Z e_l.

Translations act on these groups. Define b:Q→P by summing, for each line, all its corner coordinates. Let e:P→Z send each e_l to1, with trivial H-action on Z. The source's corner operation c:L→Q is injective (`lem:hom-corner-module`). We claim the exact sequence of R-modules

    0 → L --c→ Q --b→ P --e→ Z → 0.                 (2.1)

Here is a direct integral proof of the extra exactness; in particular, no rationalization or finite-index replacement is made. Fix a tangent orientation on each of the four directions, with its positive ray lying in a common half-open angular interval of length pi. At a point z of a line l, let J_l denote the value on its left minus the value on its right. Its difference between the forward and backward portions of l is the corresponding coordinate q_l of the corner. Indeed, reading sectors counterclockwise, write d_i for successive changes in sector value. The left-minus-right jump on the forward ray is d_i and on the backward ray is -d_(i+r). Thus its change is d_i+d_(i+r), precisely the source's coordinate. All r such coordinates sum to0.

For f of compact support, J_l vanishes at both ends of l; telescoping gives sum_z q_l(z)=0. Hence bc=0. Conversely take a finite q∈Q with bq=0. For each of the finitely many lines carrying a nonzero coordinate, set J_l to0 near its negative end and increase it by q_l(z) at each marked point z. The line sum condition makes J_l also0 near its positive end. These are integral, piecewise constant, compactly supported jumps along finitely many lines.

Integrate these prescribed jumps across the chambers of that finite arrangement, starting with value0 outside a large disk containing their supports. Local path independence at every intersection says that the sum of changes on a small loop is0. That sum is exactly sum_(l through z)(J_l(after z)-J_l(before z))=sum_l q_l(z)=0. Intersections not in the support have zero such sum as well. These local loops generate the obstruction to path independence: subdivide any bounded disk bounded by a transverse closed path by the finite arrangement, and cancel the crossings on all interior edges. Equivalently, the chamber adjacency dual complex, with its vertex-loop relations, is a cell subdivision of the plane. Thus integration is independent of the path. The resulting function is integer-valued, constant on chambers, and zero off a sufficiently large disk, since all jumps there are zero and that exterior is connected. It belongs to L and has corner data q. This proves ker b=im c. The construction also permits additional allowable lines with identically zero jump; there is no assumption that only the selected lines exist.

Every e_l-e_l' for intersecting nonparallel lines is in im b, by choosing q_l=1, q_l'=-1 at their intersection and all other coordinates0. The graph of all allowed lines joined at such intersections is connected: coordinate lines connect each other and every line of either inclined direction, and parallel lines can be joined through a coordinate line in another direction. These differences generate ker e. The last map is surjective. This proves (2.1).

### Vertex and line orbits

Every intersection involving a coordinate line is in O^2, because the relevant determinant is1 or the unit lambda. At a point in O^2 all four directions occur. The intersections of the two inclined families form

    B^(-1) O^2,   B = [[-lambda,1],[1,-lambda]].

Modulo H they have cardinality M=|Norm(det B)|=|Norm(1-lambda^2)|. This follows either from the determinant of its integral rank-four matrix or from the index of B O^2 in O^2. One of these M classes is O^2 itself. At any of the other classes neither coordinate lies in O: if one did, either inclined equation and the fact that lambda is a unit would put the other in O too. Thus the remaining M-1 classes have exactly two directions. Translation stabilizers of vertices are trivial. Consequently

    Q ≅ R^3 ⊕ R^(M-1) = R^(M+2).                  (2.2)

Each of the four line families is a single H-orbit. Its stabilizers are

    H_x = O(1,0),       H_y = O(0,1),
    H_3 = O(1,lambda),  H_4 = O(lambda,1).

The order of the two coordinate labels is immaterial. They are rank-two free abelian groups, and

    P ≅ direct sum_(i=x,y,3,4) Z[H/H_i].            (2.3)

The stabilizers act trivially on the line generators: translations preserve the chosen orientations. These facts account for all orbits and all incidence multiplicities, including the four-direction orbit.

## 3. Integral translation homology

Let K=ker(P→Z). Apply H-homology to the two short exact sequences in (2.1). Shapiro identifies H_j(H;P) with direct sum_i wedge^j H_i, and the map to H_j(H;Z)=wedge^j H is the sum of the exterior powers of the four inclusions. This is the same integral inclusion operation used in Gähler–Hunton–Kellendonk; it is not merely a map of vector-space ranks.

The degree-one map Z^8→Z^4 is surjective, already on the coordinate summands, with free kernel Z^4. In degree two the map

    B_2: Z^4 → wedge^2 Z^4 ≅ Z^6

is injective, and

    coker B_2 ≅ Z^2 ⊕ Z/d,   d=F_(2a).             (3.1)

To verify (3.1) for every a, write lambda=u+v tau, u=F_(a-1), v=F_a. Multiplication by lambda in the basis(1,tau) is [[u,v],[v,u+v]], of determinant u²+uv-v²=(-1)^a; in particular gcd(u,v)=1. In the ordered basis (x_1,x_tau,y_1,y_tau) of H, the coordinate columns are e12 and e34. Eliminating their entries from the other two columns leaves, in coordinates(e13,e14,e23,e24),

    c = (v, u+v, -u, -v)^T,
    h = (-v, u, -u-v, v)^T.                        (3.2)

The gcd of all entries is1. In row order, the six two-by-two minors are

    v(2u+v), -v(2u+v), 0, -v(2u+v), v(2u+v), -v(2u+v).

Thus their gcd is v(2u+v)>0. Smith normal form gives invariant factors1 and v(2u+v). The Fibonacci addition identity gives v(2u+v)=F_(2a). Together with the two coordinate unit columns this proves (3.1). This arithmetic is checked independently by `checks.py`; its finite runs are diagnostics, whereas the displayed identities establish the general Smith calculation.

The long exact sequence for 0→K→P→Z→0 now gives

    H_3(H;K) ≅ wedge^4 H ≅ Z,
    H_2(H;K) ≅ wedge^3 H ≅ Z^4,
    0 → coker B_2 → H_1(H;K) → Z^4 → 0,
    H_0(H;K) ≅ ker(Z^4 --sum→ Z) ≅ Z^3.

The middle extension splits as abelian groups, since its quotient is free. Hence H_1(H;K)≅Z^6⊕Z/d. Higher groups vanish above degree3. Since Q is free over R, the sequence 0→L→Q→K→0 yields

    H_2(H;L) ≅ Z,      H_1(H;L) ≅ Z^4,
    0 → Z^6⊕Z/d → H_0(H;L) → Z^(M-1) → 0.        (3.3)

For the final quotient, Q_H=Z^(M+2) maps onto K_H=Z^3; its kernel is free of rank M-1. Again the displayed extension splits because its quotient is free. Thus

    H_j(H;L) ≅ Z^(M+5)⊕Z/d  for j=0,
                 Z^4       for j=1,
                 Z         for j=2,
                 0         for j>2.               (3.4)

By the source's `lem:hom-square-induction` and `eq:hom-plane-torus`, these are H_j(Gamma;C(X,Z)), hence the homology of the transformation groupoid G=X⋊Gamma. Under the rank-two Koszul resolution, H_2(Gamma;C(X,Z)) is the subgroup of functions invariant under both generators. Minimality makes such a locally constant integer function constant. Its generator is exactly 1_X, not an unspecified nonzero multiple.

## 4. A stable lift of the top class

Write E=K(B_G), the connective bisection spectrum in Li's construction. Its reduced stable integral homology is H_*(G) by Theorem4.18; below H_*(E) always means that reduced stable homology. The source's polygon category B is the same category up to symmetric monoidal equivalence: an object is a finite list of clopens and a morphism is a compact open bisection between their disjoint unions, namely a finite piecewise translation with track changes. Its explicitly described strings C_p resolve B.

We construct a map of connective spectra

    j: Sigma^infinity (B Gamma)_+ → E             (4.1)

whose homology map is induced by the invariant coefficient inclusion Z→C(X,Z),1↦1_X. The full spectral map, and not only a map of homology groups, is essential.

Here are its objects and coherences. Let D_p be the symmetric monoidal groupoid of finite Gamma^p-indexed sets with finite support and fiberwise bijections. Its face functors sum fibers when labels merge. For the first and last faces one forgets the first or last label; inner faces add adjacent labels; degeneracies insert0. It is the degreewise free symmetric monoidal category on the nerve of the one-object group Gamma.

Map D_p→C_p by replacing the finite fiber at (gamma_1,...,gamma_p) by a constant copy over **all of X**, and following the trajectory

    x, x+gamma_1, ..., x+gamma_1+...+gamma_p.

The first face translates its initial clopen X to X. Thus it still has the same constant fiber, and is exactly the first face in D_p. The inner faces compose translations by adding increments, and the last face forgets the last increment. Fiber sums and permutations are preserved. The canonical reorderings of finite lists provide the symmetric monoidal coherence; alternatively finite labeled sets rather than an ordered skeleton make the identifications literal. Hence this is a simplicial symmetric monoidal functor, with no chosen partition varying incompatibly under translation.

At any fixed degree p, K(D_p) is a wedge of sphere spectra indexed by Gamma^p. This is the free-finite-set category identification used in Li Lemma4.5 (the finite case), extended over finite subsets by filtered colimits. A map of label sets induces the corresponding fold of sphere summands. Therefore its realization is Sigma^infinity(B Gamma)_+.

The source's commuting-grid proof of `lem:hom-string-resolution` is natural in its bar indices. Applying that same proof with any number n of bar indices gives a realization equivalence |B^n C_p|≃B^n B: normalize multi-interval objects to their ordered elementary entries, retain all horizontal exchange maps, and use the constant-vertical-string inclusion with the explicit ladder formula a_i=w_(0i)a_0 v_(0i)^(-1). Each inclusion commutes with the bar faces and degeneracies, and therefore also with the structure maps that add a bar. Passing to the connective spectrum gives |K(C_p)|≃E. This is a uniform use of the **paid** grid normalization, not a new homotopical stability assertion for fixed-track groups.

Composing the realized functor with this equivalence constructs(4.1). Its effect on ordinary integral spectrum homology can be checked before realization: each sphere generator at (gamma_1,...,gamma_p) is sent to the constant multiplicity function 1_X in that summand. The faces are precisely the source's `eq:hom-trajectory-faces`; in particular d_0 acts by translation on coefficients, and fixes1_X. Thus the resulting chain map is the group bar map

    [gamma_1|...|gamma_p] ↦ 1_X [gamma_1|...|gamma_p].

This identifies its effect under Li's homology theorem without assuming that an arbitrary stable Hurewicz map is surjective. Equivalently it is the stable adjoint of the global-translation functor B Gamma→B B→Omega^infinity E, keeping the component of X.

For Gamma≅Z^2, B Gamma is the two-torus. Its suspension spectrum splits as

    Sigma^infinity(T^2)_+ ≃ S ∨ Sigma S ∨ Sigma S ∨ Sigma^2 S.

For completeness, S^1_+ splits stably as S∨Sigma S: collapse to S^0 has the section choosing the circle's basepoint, and the quotient is the based circle. Smash two copies and distribute the finite wedge. The last sphere's H_2 generator is the torus fundamental class. Its image in H_2(E) is the cycle 1_X([s|t]-[t|s]) for the two generators s,t of Gamma, which corresponds to1_X under the Koszul resolution and generates H_2(E)≅Z. Consequently

    pi_2(E) → H_2(E) is surjective.                (4.2)

This is the operation that pays the possible degree-two stable attaching obstruction. A rational computation, or a rank count in(3.4), would not prove(4.2).

## 5. Splitting and the two-primary extension

We use the following elementary connective-spectrum lemma. Suppose Y is connective with

    H_0(Y)=Z^r⊕Z/d, H_1(Y)=Z^s, H_2(Y)=Z,
    H_i(Y)=0 for i>2,

and pi_2(Y)→H_2(Y) is onto. Then

    Y ≃ S^vee r ∨ M_d ∨ (Sigma S)^vee s ∨ Sigma^2 S,       (5.1)

where M_d is the cofiber of d:S→S; M_1 is contractible. Indeed pi_0(Y)≅H_0(Y). Choose maps from r sphere summands realizing its free generators. A generator x of its cyclic summand satisfies dx=0 in pi_0(Y), so a chosen nullhomotopy extends its sphere map over M_d. The stable Hurewicz map pi_1(Y)→H_1(Y) is onto; for example the connective Atiyah–Hirzebruch edge sequence used by Li in Theorem6.12 gives this assertion. Choose s lifts of a free basis of H_1, and a lift of the H_2 generator by hypothesis. They define a map from the wedge in(5.1) to Y inducing an integral homology isomorphism in every degree. Its cofiber is connective and integrally acyclic, hence contractible: a lowest nonzero homotopy group of a bounded-below spectrum is detected by the stable Hurewicz theorem. This also explains why there are no unexamined higher attaching maps in(5.1).

Apply this to E using(3.4) and(4.2), with r=M+5, s=4, d=F_(2a). Thus

    pi_2(E) ≅ Z ⊕ (Z/2)^(M+9) ⊕ pi_2(M_d).        (5.2)

The finite term must still be computed as a group, not merely by its order. If d is odd, multiplication by d is an isomorphism on pi_1(S)=pi_2(S)=Z/2; the cofiber sequence gives pi_2(M_d)=0. If 4 divides d, it gives an extension of Z/2 by Z/2. To resolve it, Saihi Theorem3.2 identifies pi_2(M(A)) with the exact-couple group A' in

    0 → A/2 --alpha→ A' --beta→ A[2] → 0,

with doubling equal to alpha composed with the natural map A[2]→A/2 composed with beta (the relation alpha beta=2 of Lemma2.4, with its domains made explicit). For A=Z/d and4|d, the nonzero element d/2 of A[2] lies in2A. Thus every element of A' has double0. The group has order4, so A'≅(Z/2)^2. This excludes Z/4. For contrast, if d≡2(mod4), the same doubling relation gives Z/4; that case cannot simply be ignored in an arbitrary cyclic Moore-spectrum calculation.

The Fibonacci recurrence modulo2 has period3, with F_n even exactly when3|n. Thus d=F_(2a) is odd if3 does not divide a. If3|a,6|2a; the addition formula proves F_k divides F_(rk) for all positive r by induction, and F_6=8. Hence8|d, in particular4|d. Substituting these two cases into(5.2) gives precisely the predicted exponent M+9+2 epsilon.

Finally lambda has norm(-1)^a and trace L_a. Thus

    Norm(1-lambda^2)=2-(lambda^2+bar(lambda)^2)
                       =2-L_a^2+2(-1)^a.

For every positive a this is negative (at a=1 it equals-1; the powers then increase the sum of squared conjugates). Taking its absolute value gives M=L_a^2-2(-1)^a-2. No asymptotic estimate was used.

## 6. Return to every fixed A_m

The ample Hausdorff groupoid G=X⋊Gamma is minimal and has no isolated units, by source geometry. It has comparison: the source's strict-area comparison embeds any clopen of smaller area into one of larger area. In the usual invariant-measure definition, if all invariant measures compare two clopens, the particular area measure does so, and the source embedding suffices. The same statement holds on finite track amplifications, using their sum area measure.

Li Corollary5.20 identifies the integral homology of D(G) with that of the universal cover of Omega^infinity_0 E. The same applies to the finite track amplification G_m. The category of finite lists of clopens for G_m is symmetrically monoidally equivalent to that for G: flatten track labels together with list labels in one direction, and regard a clopen of X as lying in a designated track in the other. The finite sums admit arbitrary numbers of list entries, so this is an equivalence for each m>=1, not only a stabilization limit. Thus its spectrum is E. Source `thm:simplicity` identifies D(G_m)=A_m for every m. The ordinary Hurewicz theorem for the simply connected universal cover gives

    H_2(A_m;Z) ≅ H_2(universal cover of Omega^infinity_0 E;Z)
               ≅ pi_2(E).

Together with(5.2) and the Moore calculation, this proves the unchanged formula for every permitted a and every finite m>=1.

## 7. Validation and limits

The substantive author checks are general: exactness in(2.1) includes local path independence and the condition at both ends of every line; orbit counting includes the exceptional four-line class; the Smith computation keeps torsion; the stable lift is constructed as a compatible simplicial monoidal functor; the spectrum lemma checks all homology and bounded-below conservativity; and the Moore calculation resolves the order-four alternative explicitly. Finite exact arithmetic diagnostics are supplied separately and cannot prove any of these geometric, categorical, or infinite-scope statements.

The most exposed review point is Section4: the spectrum-level realization and its constant-fiber map must agree with the paid trajectory resolution, not just with an abstract isomorphism of homology groups. The argument gives the actual functor, all faces, the compatible grid comparison, and its chain map for this reason. Section5 does not infer stable splitting from homology alone; its extra Hurewicz hypothesis is supplied in Section4.

This is a complete author proof submission, not an assertion that the contribution gate passes. Fixed-track homology invariance is Li's result, the stratum method and exterior-power computation are classical, and the general Moore operation is Saihi's. Source253's simple amenable finitely presented groups and its explicit categorical resolution are credited in full. The claimed additional calculation is the exact integral multiplier with its resolved stable obstruction and arithmetic parity. Whether that constitutes an eligible substantial operation, rather than a technical combination of paid operations, is expressly left to independent review. No original-work claim is attached to the general toolkit.

Original prose: CC BY4.0. Original diagnostic/control code: MIT. Third-party reading copies remain under `private/` and are not part of any original-work redistribution. No publication operation was performed.
