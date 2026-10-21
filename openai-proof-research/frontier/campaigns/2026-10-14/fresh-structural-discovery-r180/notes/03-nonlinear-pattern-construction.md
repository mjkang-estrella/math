# r180: nonlinear chamber patterns and the exact missing equality

This is a prefreeze construction and calculation. No claim that nonlinear patterns are new homeomorphism types is frozen or asserted.

## 1. Define every space and marking

Fix the SAME authenticated Source320 data A, panel labels a_s, (P2,S2), V, j, θ and Q2; n=dim A≥2. For an arbitrary function c:A→F2 take one fixed copy V_b of V for every b∈A. On its boundary put h_b=θ^{c(b)}, and on its interior use j_b=θ^{c(b)}j. Define M_c as the quotient of the finite disjoint union of these V_b by the following relation: interior points have no new identifications, while

    (b,v)∼(b',v') iff h_b(v)=h_b'(v')=:y
                         and b-b' lies in A(J(y)).              (3.1)

Here J(y) is the set of downstairs panels containing the projection of y and A(J(y)) is their label span. Define

    f_c:M_c→Q2,       [b,v]↦[b,θ^{c(b)}j(v)].                    (3.2)

The quotient relation, not an assumed cocycle or a guessed wrapper, defines this operation.

For fixed y, A(J(y)) is a subgroup, so (3.1) is transitive. Its finitely many closed chamber-pair relations imply Hausdorffness by the same compact quotient argument as source models.tex. There are no identifications between different points in one chamber because h_b is injective. In h_b-coordinates a neighborhood at a q-panel point consists of 2^q orthants, since the q incident labels are independent. Label translation switches the corresponding signs. Their union is a neighborhood in R^4. This chart argument needs no linearity of c: each incident chamber has its OWN collar coordinate h_b. Thus M_c is compact and locally Euclidean, without boundary. The chamber adjacency graph is connected because the panel labels span A and every panel has nonempty lift; each V_b is connected. Hence M_c is closed and connected.

For the homotopy comparison, order the finitely many chambers. At each attachment the boundary subset in P2 is a union K_b of lifted panels, while its preimage in V_b is h_b^{-1}(K_b). These inclusions are cofibrations by the same finite panel/collar construction as in the source. On the attaching subset the map is exactly h_b, not just homotopic to it. The map on the new chamber is j_b, a homotopy equivalence. Induction using the homotopy pushout comparison proves (3.2) is a homotopy equivalence. Asphericity, π1=Π, and orientability therefore follow from Q2. No inference about connected sums or arbitrary gluings is used. This construction is a direct extension of the source chart/gluing proof, so construction alone is paid-level composition.

## 2. Exact translations and their algebra

Let

    U_c={a∈A: D_a c(b):=c(b+a)+c(b) is independent of b}.

For a∈U_c denote that constant by d_c(a). The identity

    D_{a+a'}c(b)=D_ac(b+a')+D_{a'}c(b)

shows U_c is a subspace and d_c:U_c→F2 is linear. In particular d_c(a)=c(a)+c(0). The maps

    T_a:[b,v]↦[b+a,v],       a∈U_c,

preserve (3.1), obey T_aT_a'=T_{a+a'}, and are faithful on chamber interiors. Equation (3.2) gives

    f_c T_a=(a,d_c(a)) f_c.

Thus the genuine action realizes the graph

    P_c={(a,d_c(a)):a∈U_c}≤R_Mc,

and note 02 yields the rigorous bounds

    P_c⊂P(M_c),       P(M_c)∩⟨δ⟩=0,       dim P(M_c)≤n.         (3.3)

These are not equalities unless the lower bound has dimension n.

There are immediate identifications among patterns, which must be divided out before proposing any count. Adding a constant t to every c(b) leaves (3.1) literally unchanged: applying θ^t to both sides does not change the equality or the panel subgroup. It changes f_c by the target δ^t. Also translating the input b gives a relabelling homeomorphism. More precisely, if d(b+a)=c(b)+t for every b, the copywise identity [b,v]↦[b+a,v] defines M_c≅M_d and intertwines the markings with (a,t)∈F. This does not imply δ is induced by a self-homeomorphism with a FIXED marking; the two markings themselves differ.

The no-extension result in the actual I97 original further shows why a direct chamberwise shortcut stops at the same condition. Suppose a proposed homeomorphism is required to carry chamber b to b+a and to induce EXACTLY the target boundary coordinate change y↦θ^t y. Its restriction k_b:V→V would have boundary

    k_b|S2=θ^{c(b+a)+c(b)+t}.

If that exponent is one at any b, it would extend θ over the graph filling V, excluded by the paid relative height argument (no finite-order assumption). Thus the condition D_a c=t is necessary for this exact chamberwise ansatz. This says nothing about an arbitrary homeomorphism, which need not preserve these chambers, nor about a map having only the same outer automorphism.

## 3. A fully specified quadratic test family

Choose a basis x1,…,xn for A*. For 1≤r≤floor(n/2), set

    q_r(b)=Σ_{i=1}^r x_{2i-1}(b)x_{2i}(b).

More generally take c=q_r+ℓ+t with ℓ∈A* and t∈F2. Its polar form is

    B_r(a,b)=Σ_i [x_{2i-1}(a)x_{2i}(b)+x_{2i}(a)x_{2i-1}(b)],
    D_a c(b)=B_r(a,b)+q_r(a)+ℓ(a).

The derivative is constant exactly when a belongs to

    U_r=⋂_{j=1}^{2r} ker x_j,

the radical of B_r. On U_r, q_r vanishes, so d_c=ℓ|U_r. Therefore the explicit translation group has dimension n-2r, with exact graph P_c=graph(ℓ|U_r). All these spaces still have the same Π and homotopy type, by §1.

For r=1 and ℓ=0 the lower bound is U={x1=x2=0}×{0}. There are precisely four full graph complements B_ε containing this U, namely

    ε=0, x1, x2, x1+x2.

All four are compatible with (3.3). For general r there are 2^{2r} extensions ε of ℓ|U_r to A. Hence the finite-group reduction does not even exclude a profile equal to a source linear model's profile.

This is an algebraic compatibility calculation, not a manifold counterexample or an assertion that any such profile is actually attained by the nonlinear model. The abstract possibility R=B_ε satisfies all the proven group bounds. Therefore a proof that the smaller visible symmetry group equals the entire realized Sylow image requires a new geometric argument.

## 4. The proposed distinct operation and its failure to close

A possible genuinely new operation would be geometric recognition of the nonlinear defect, invariant under EVERY unmarked homeomorphism of M_c, or a computation of the full profile P(M_c) showing a value unavailable among the source linear models. The fully specified first test is c=q_1=x1x2. A sufficient new equality would be

    P(M_q1)=ker(x1)∩ker(x2)×{0}.                               (3.4)

If proved, (3.4) would separate this model from every linear Mε. But the necessity argument in §2 only treats exact chamberwise maps; it does not prove (3.4). We do not freeze it as a theorem, claim it is true, or call it a necessary route to every possible result. Note 04 carries the strongest available surgery/core operations through this test rather than leaving (3.4) as an unexplained named gap.
