# I195 analytic attempt

Status: COMPLETE written assignment, PARTIAL mathematical resolution. Sections 1–5 are finalized; original-target verdict UNRESOLVED at J195. Earlier partial versions were updated incrementally. This is an unsealed proof-only record; no research code or enumeration has been used.

## 1. Domain, exact residual, and scope

All spaces are over Q; an edge or object in a vector expression denotes its incidence vector. Let B consist of finite simple cubic bipartite planar 3-vertex-connected graphs with a specified embedding. A B-admissible step deletes disjoint facial edges e=uv,f=xy in terminal order u,v,...,y,x,... and inserts arms up,vq,xr,ys and square pq,qs,sr,rp on four new vertices, producing H in B. The brace restriction additionally requires both graphs to extend every pair of disjoint edges to a perfect matching. No all-brace generation theorem is assumed.

Set K=G−{e,f}, D_G=diff(HC(G)), d(G)=dim D_G. Here diff is the span of pairwise differences and is zero on an empty or singleton family. Nij are the COMPLETE old Hamiltonian families of deleted-edge signatures (i,j). S=N10∪N01∪N11; L=diff(S); L0=diff(N10)+diff(N01)+diff(N11); V=diff(N00). The COMPLETE new exterior classes are spanning ux paths Pux, spanning vy paths Pvy, and spanning two-path covers D11 with pairing uv,xy and no cycle components. Put

    U=diff(Pux)+diff(Pvy)+diff(D11),
    ell=d(G)−dim L, t=dim(L+U)−dim L.

All six surviving/new classes are nonempty: the read cor:pfaffian-paths (manuscript 812–828) applies to H. Its paths p-r-s-q, r-p-q-s, p-q-s-r, q-p-r-s force N10,N01,Pux,Pvy; closing just the square is not spanning. The paths u-p-r-x and u-p-q-v force respectively D11,N11 by saturating the indicated square vertices. This supplies existence, not a rank theorem.

Choose C0∈S, Aij∈Nij for ij=10,01,11, and P∈Pux,Q∈Pvy,D∈D11. Define

    b=P+Q+D+2e+2f−3C0,
    beta=P+Q+D+2e+2f−A10−A01−A11,
    eta=dim(L0+U+<beta>)−dim(L0+U) ∈ {0,1}.

With N∈N00, define c=N−A10−A01+A11 and r=N−C0. Both c,beta lie in ker A_K, with zero deleted coordinates. The three surviving signatures affinely span Q²; a surviving difference with zero deleted coordinates has zero total coefficient separately in each class. Therefore L∩{e=f=0}=L0, dim L=2+dim L0 and dim(L+U)=2+dim(L0+U). Also b−beta∈L. The paid R168/F169 identities give

    d(G)=2+dim(L0+V+<c>),
    d(H)=2+dim(L+U+<b>),
    d(H)−d(G)−2=t+eta−ell=eta−Delta.             (1)

The child projection is (arm_up−arm_vq,square_pq−arm_xr), with new-family images (1,0),(−1,1),(0,−1); their sole relation is their sum, whose pullback is b. This retains the cross-class offsets in (1). No within-class-only substitution is being made.

Let A_arc be the odd u-to-x complementary facial arc and B_arc the odd v-to-y arc, of lengths 2k_A+1,2k_B+1. Their alternating sums q_A,q_B start and end with +1. For J=Pux,Pvy,D11 put q_J=q_A,q_B,q_A+q_B respectively. Define F_J={N'∈N00:N'−q_J is a 0/1 object of J} and R_J={X∈J:X+q_J∉N00}. If F_J≠∅ choose X_J=N_J−q_J from its image and E_J={X−X_J:X∈R_J}; otherwise choose X_J∈J and E_J={X−X_J:X∈J}. Then

    diff(J)=diff(F_J)+span E_J,
    V_good=Σ_J diff(F_J), R=span(∪_J E_J), U=V_good+R,
    delta_V=dim(L0+V)−dim(L0+V_good),
    delta_R=dim(L0+V_good+R)−dim(L0+V_good),
    epsilon=dim(L0+V+<c>)−dim(L0+V) ∈ {0,1},
    Delta=ell−t=delta_V+epsilon−delta_R.           (2)

I192's proved facial classification is F_Pux=N00 exactly when k_A=0, otherwise empty; F_Pvy similarly with k_B; F_D11=N00 exactly when both k's vanish, otherwise empty. It follows by deleting disjoint selected facial edges of one Hamiltonian cycle: the complementary disk's noncrossing endpoint matching is the cyclically shifted adjacent pairing. Alternating subtraction closes one extra component at each negative edge. Thus on genuine long gaps k_A,k_B≥1,

    V_good=0, R=U, delta_R=t,
    delta_V=dim(L0+V)−dim L0, ell=delta_V+epsilon. (3)

In particular absence of translated old objects DOES NOT imply U∩V=0, or either containment. Other linear combinations can recover directions. I170's paid obstruction to V⊆L+U remains binding.

For all lengths retain the full bridge extension

    s_arc=e+f−q_A−q_B,
    a_P=P+q_A−N, a_Q=Q+q_B−N,
    a_D=D+q_A+q_B−N,
    b=3r+2s_arc+a_P+a_Q+a_D.                     (4)

Adding the displayed vectors proves this identity. The three a-vectors have zero degrees in K. On long gaps their completions are not old Hamiltonian cycles; they can even have non-Boolean coordinates. No a-term can be discarded on that basis. Anchor changes alter the bridge only inside the stated spaces.

If N00=∅, ell=0 and (1) settles exchange without introducing N,c,r or epsilon. Otherwise J192 on long gaps is exactly Delta≤1 and, when Delta=1, beta∉L0+U.

## 2. Polygonal-face prism family: admissibility and complete families

Let m≥8 be even. Vertices are T_i,B_i, indexed modulo m; edges are t_i=T_iT_(i+1), b_i=B_iB_(i+1), rho_i=T_iB_i. Use the usual prism embedding and its top m-gon. Delete e=t_0 and f=t_j with even j, 4≤j≤m−4. Set u=T_0,v=T_1,y=T_j,x=T_(j+1). The two arc lengths are

    a=m−j−1=2k_A+1, b_len=j−1=2k_B+1,
    k_A=(m−j−2)/2, k_B=(j−2)/2.

Both are at least three. These parametrize every requested odd-arc cap deletion up to cyclic relabeling and reversal. The first case is m=8,j=4 (3+3).

The prism is simple, cubic, bipartite and plane. Two vertex deletions in one layer leave the other layer intact and all surviving vertices attached; one deletion in each layer leaves two paths connected by a remaining rung. Hence it is 3-connected. It is also a brace: two rungs extend to all rungs; a rung and a disjoint rail extend using that rail and its counterpart plus remaining rungs; two disjoint same-layer rails extend with both counterparts and remaining rungs; two opposite-layer rails extend independently to the alternating perfect matching of each layer containing its prescribed rail.

The child is B-admissible. The terminal colors alternate in cyclic order because j is even; the four arms and square admit the required bipartition, and embed inside the cap. Simplicity and cubic degree are immediate. Here is the complete 3-connectivity argument, reused at I193's exact scope. Two old vertex deletions leave a connected parent remainder whose surviving e,f routes can be replaced through the intact square, which attaches to at least two terminals. Two new vertex deletions leave the old graph K connected, and each surviving new vertex has its arm. To justify K connected, a cubic simple 3-connected graph has no edge cut of size ≤2: each side would have at least three vertices, and deleting the at most two boundary vertices on one side would contradict 3-connectivity. For one old and one new deletion, the three surviving square vertices form a path. If the old vertex is a terminal, the parent minus it is 2-connected and removing the other selected edge leaves it connected. Otherwise each component of (G minus that old vertex)−{e,f} meets at least two terminals; one would give a bridge in the 2-connected parent-minus-vertex and zero would already be disconnected. The three remaining arm attachments meet every component and join them. Fewer deletions are included. We claim B-admissibility; no assertion of child bracehood is needed or used for this family theorem.

Write T=Σ_i t_i, Btm=Σ_i b_i, Z=T+Btm. The complete old Hamiltonian family is

    C_i=Z−t_i−b_i+rho_i+rho_(i+1) (0≤i<m),
    X=Σ_(i even)t_i+Σ_(i odd)b_i+Σ_i rho_i,
    Y=Σ_(i odd)t_i+Σ_(i even)b_i+Σ_i rho_i.

Exhaustion: in a nonempty proper selected-rung set, the omitted rails in each layer form the unique matching of each even run of selected rung vertices. Both layers omit the same positions. Two or more such positions split the degree-two subgraph into multiple components, so exactly one position is omitted, giving C_i. With all rungs, each layer's used rails are an alternating perfect matching; equal matchings give disjoint squares, opposite ones give X,Y. No rungs gives two layer cycles. Consequently

    N00={Y}, N10={C_j}, N01={C_0},
    N11={C_i:i≠0,j}∪{X}.                         (5)

The six child classes consist of the last three and the following three COMPLETE families. Put I_B={1,...,j−1}, I_A={j+1,...,m−1}, and d_i=rho_i+rho_(i+1)−t_i−b_i, so C_i=Z+d_i. Define fixed vectors

    P*=Z−Σ_(i=0,2,...,j)t_i−Σ_(i=1,3,...,j−1)b_i
           +Σ_(i=1,...,j)rho_i,
    Q*=Z−t_0−Σ_(i=j,j+2,...,m−2)t_i
           −Σ_(i=j+1,j+3,...,m−1)b_i
           +rho_0+Σ_(i=j+1,...,m−1)rho_i.

Then the lists are exactly

    Pux={P_g=P*+d_g:g∈I_A},
    Pvy={Q_h=Q*+d_h:h∈I_B},
    D11={D_hg=Z−t_0−t_j+d_h+d_g:h∈I_B,g∈I_A}.  (6)

These are vector formulas for Boolean edge sets, not signed candidate objects requiring a later unspecified filter. In particular their cardinalities are a,b_len,a*b_len, respectively.

Here is a complete exhaustion and connectivity proof of (6). Any path or cover in question has degree two at every B_i. Its omitted bottom edges form a nonempty matching I on the index cycle: two omissions at one B_i would leave degree at most one, and zero omissions would retain the whole bottom cycle. The rung at i is used exactly when i is an endpoint of an edge of I. Let J be the omitted top positions, including 0,j, and put x_i=1_J(i)−1_I(i). If E is the set of prescribed top endpoints, the top degree equations are exactly

    x_(i−1)+x_i=1_E(i).                           (7)

The value x_0=1−1_I(0) is 0 or 1; (7) uniquely determines every other value.

For Pux, E={0,j+1}. If x_0=1, x_i=(-1)^i on 0≤i≤j and zero on I_A. Thus I contains exactly the odd positions 1,3,...,j−1 on that segment, J exactly its even positions, and all further omissions are common positions on I_A. Without a common omission, there is the exterior top path with endpoints 0,j+1 and a separate closed component through the bottom layer and the zigzag inside 1,...,j. A common omission g cuts the corresponding top and bottom edges and adds both incident rungs, joining the two pieces into one spanning path. With r≥2 common omissions, consecutive omissions along I_A enclose a separate ladder cycle; equivalently cutting both parallel routes into r pieces and joining their matching ends leaves r−1 closed components and the endpoint path. Thus precisely one common omission is allowed, giving P_g. The forced bottom omissions and g are disjoint for every g∈I_A.

If x_0=0, the alternating segment is instead I_A, with +1 at odd positions and −1 at even positions. Common omissions occur on {0,...,j}, and both 0 and j are compulsory. The same two-route tracing leaves at least one closed component (there are at least two common omissions), so there is no spanning path. This excludes the second solution entirely. Interchanging the complementary arcs and the two endpoint pairs gives precisely Q_h; alternatively (7) has alternating values +1 on even positions of {j,...,m−1,0}, −1 on its odd positions, and zero on I_B, requiring exactly one common omission h∈I_B. Its alternative again requires both 0 and j as common omissions and fails connectivity.

For D11, E={0,1,j,j+1}. If x_0=1, only x_0=x_j=1 are nonzero. Hence J=I∪{0,j}, with 0,j∉I. Common omissions I lie on the two arcs. Two common omissions in the same arc leave a closed ladder component between consecutive ones, so at most one in each arc is allowed. No common omissions leave the bottom cycle. Exactly one common omission gives two paths paired ux,vy, the wrong pairing. Exactly one h∈I_B and one g∈I_A gives the required pairing uv,xy: the bottom segment between the cuts joins one half of each top arc, and the complementary bottom segment joins the other halves. All vertices belong to these two paths. Thus precisely the D_hg are valid.

If x_0=0, (7) gives x_i=+1 for odd i, −1 for even i other than 0,j, and zero at 0,j. Since 0,j must be common omissions, I is every even position and J is every odd position together with 0,j. The object is exactly X−e−f. It consists of the two paths paired ux,vy, not uv,xy: along each segment between successive selected facial edges e,f of X the endpoints are the shifted adjacent pairing. Directly following the alternating rail/rung cycle X gives the same result. This excludes the other solution and completes exhaustion. These arguments are written classifications, not a matching or graph scan.

## 3. Prism ranks, exact margin, and bridge

The m+2 old cycles are affinely independent. In an affine dependence with coefficients c_i,x,y and total zero, top-minus-bottom rail coordinates force x=y. With s=Σ c_i each rail equation gives c_i=s+x; total zero gives s=−2x, so c_i=−x and (m−2)x=0. Hence every coefficient vanishes. It follows that

    d(G)=m+1, dim L=m, dim L0=m−2,
    V=0, ell=1, delta_V=0, epsilon=1.             (8)

The epsilon assertion follows also directly: Y is outside the surviving affine hull, and the signature reduction (1) says c supplies precisely that extra dimension.

By (6), differences in Pux are C_g−C_g', those in Pvy are C_h−C_h', and differences in D11 are sums of these. Therefore

    U=span{C_g−C_g':g,g'∈I_A}
       +span{C_h−C_h':h,h'∈I_B} ⊆ L0,
    dim U=(a−1)+(b_len−1)=m−4,
    t=delta_R=0, Delta=1.                        (9)

Independence and the direct-sum dimension in (9) follow from old affine independence and disjoint index sets. All three residual classes are nonempty and can have many directions, but they add zero rank modulo L0. The inequality Delta≤1 is sharp: margin 1−Delta=t−(ell−1)=0 for every member of this infinite family.

The bridge is nevertheless independent. From the explicit fixed vectors,

    P*+Q*=Z+Y−e−f,
    P_g+Q_h=D_hg+Y.                              (10)

This follows by comparing the top even rails (0,j counted twice), the bottom odd rails, and all rung coordinates. Choose the aligned P_g,Q_h,D_hg, and any A11∈N11, with A10=C_j,A01=C_0. Then

    beta=2C_h+2C_g−2Z+Y−C_j−C_0−A11.            (11)

Indeed D_hg+e+f=Z+d_h+d_g=C_h+C_g−Z. The exact identity

    (m−2)Z=Σ_i C_i−X−Y                           (12)

is verified by summing: Σ C_i=(m−1)Z+2Σ rho_i and X+Y=Z+2Σ rho_i. Substituting (12) into (11) is an affine-difference combination (coefficient sum zero) whose Y coefficient is

    1+2/(m−2)=m/(m−2)>0.                         (13)

Let w be the unique functional on D_G annihilating L and taking value 1 on Y−C0 for a surviving base C0. It exists by (8) and old affine independence. Equations (11)–(13) give w(beta)=m/(m−2). Since U⊆L0⊆L, beta∉L0+U, eta=1, and

    d(H)=m+3=d(G)+2.                             (14)

This also settles the equality bridge for every member of the family; changing anchors changes beta only by L0+U and cannot change (13).

For the smallest case m=8,j=4, the ten old cycles are C_0,...,C_7,X,Y. Precisely Y is lost; N10={C_4}, N01={C_0}, N11={C_1,C_2,C_3,C_5,C_6,C_7,X}. The new families are P_5,P_6,P_7; Q_1,Q_2,Q_3; and the nine D_hg with h∈{1,2,3},g∈{5,6,7}, given explicitly by (6). Thus the six child-family sizes are 1,1,7,3,3,9 (24 child cycles), d(G)=9, dim L=8, dim L0=6, dim U=4, ell=1,t=0,epsilon=1,Delta=1,eta=1, w(beta)=4/3, d(H)=11. These exact values come solely from the written complete lists and their independence proofs; no enumeration was run here.

## 4. Multi-component routes: exact statements and unpaid steps

### 4.1 Booleanity precedes every two-factor claim

The long-arc signed completions must not be silently treated as graph objects. For Q∈Pvy there are two useful, distinct conditional constructions.

First, if Q avoids all positive edges of q_B and uses all its negative edges, F_B=Q+q_B is Boolean and is a spanning two-factor in K with exactly k_B+1 components. To prove the count, draw an auxiliary v-y edge c inside the face on the B_arc side, so Q+c is a Hamiltonian cycle in an auxiliary plane graph. The k_B negative B_arc edges and c are disjoint facial edges of this cycle. Remove them. I192's noncrossing matching lemma gives the shifted endpoint pairing; each of the k_B+1 positive B_arc edges closes exactly one of the resulting paths. This proves the component count. If the specified presence/absence pattern fails, Q+q_B has a coordinate −1 or 2 and is not a two-factor. No universal claim that this construction is Boolean has been proved.

Second, if Q uses all positive A_arc edges and avoids all negative ones, F_A=Q−q_A+e+f is Boolean and is a spanning two-factor in G with exactly k_A+2 components. Close Q by an auxiliary v-y chord on the other side, leaving A_arc,e,f on one facial boundary. The selected edges of Q+c are the k_A+1 positive A_arc edges and c. Removing them gives k_A+2 paths. Their intervening gaps are the k_A negative A_arc edges and e,f; adding those closes each path separately by the same matching lemma. This proves the exact count. For k_A=0 it specializes to the paid two-component factor Q−a+e+f. This construction and F_B are different operations, with different component counts; “remove positive arc edges and add e,f” also requires adding the negative arc edges to preserve degrees. The brief's suggested multi-component route is used only in these precise Boolean cases, with the operations and indices explicit.

The auxiliary graph is used solely for the elementary planar matching lemma, which requires a Hamiltonian cycle and a facial boundary, not cubicity, bracehood or an upstream existence theorem. Its temporary chord is a proof device, not a source copy or a new computational graph instance. No external result is invoked.

On the prism family every Q_h satisfies the second pattern, because all odd A positions are used top rails and all even A positions are omitted. The resulting factor has k_A+2 components. This is a written specialization of (6), not an additional finite run. By contrast, Q_h+q_B is never Boolean on a genuine long gap in this family: Q_h omits just one B_arc top edge h, whereas q_B has at least two positive edges, so at least one positive coordinate would become 2. Thus even this settled family requires keeping the distinction between the two constructions.

### 4.2 Flip connectivity for multiple components

Let T be any spanning two-factor with h components, and R a simple T-alternating cycle. Suppose its q removed T-edges meet c components of T. Removing them leaves q paths on the touched components and h−c untouched cycles. Let tau pair the endpoints of those paths and mu pair the endpoints of the added edges. Suppressing paths preserves components and leaves the untouched cycles separate. Exactly

    components(T triangle R)=h−c+components(tau∪mu). (15)

The union on the right is a 2-regular multigraph, including doubled edges. This is a complete proof by tracing a path followed by an added edge. In particular Hamiltonicity requires c=h and tau∪mu connected; merely reducing a degree defect or selecting an alternating cycle does not ensure either condition. For Hamiltonian T, h=c=1 and (15) is precisely I194's criterion. This extension is bookkeeping, not a guarantee of a reconnecting R.

For any two spanning two-factors F,T in a cubic graph, their symmetric difference is a disjoint union of alternating cycles R_i, with increments v_i. For T=C Hamiltonian put T_I=C+Σ_(i∈I)v_i. If nonnegative rationals theta_I supported on Hamiltonian T_I satisfy Σ_(I containing i)theta_I=1 for every i, then

    F−C=Σ_I theta_I(T_I−C).                       (16)

This is the paid fractional block proof and it is independent of the number of components of F. The sum is taken before applying any quotient functional, so no undefined evaluation of a non-Hamiltonian intermediate difference occurs. However, (16) only produces a combination of OLD Hamiltonian differences. The long-gap obligation compares their span against L+U. Without controlling the cosets of the T_I−C, (16) gives no lower bound for t. The short-gap proof could use a single normalized lost-family indicator; Section 4.4 below explains why it is absent here.

No successful-block cover is constructed for arbitrary F_A or F_B. I194's cube obstruction shows that this particular certificate is not universally forced even for a brace in the previously paid scope. It is not a long-gap counterexample, and I do not claim that obstruction alone disproves existence of all long-gap covers. Chains with Hamiltonian proper prefixes again leave a last jump to disconnected F unpaid. A count of components does not control that jump's quotient value.

### 4.3 Matching extension and the bridge's a-objects

For any actual spanning two-factor F in a cubic bipartite graph, its complement M0 is a perfect matching. Alternating each even component splits F=M1+M2 into two perfect matchings, with independent phases on its h components. Let F01=M0+M1 and F02=M0+M2. Then

    F+F01+F02=2E(G).                             (17)

There are 2^(h−1) phase choices up to swapping M1,M2. Every union is degree two, but may be disconnected. The brace axiom guarantees a perfect matching containing two specified disjoint edges; it neither fixes this entire M0 nor says any of these unions is connected. If both unions happen to be Hamiltonian, (17) gives an identity involving two old cycles, with the additional direction 2E(G)−3C0 still to be valued. If either is disconnected, it cannot be inserted in an old HC difference span without a separate argument. Thus neither the number of phases nor two-edge extension supplies independent directions of U modulo L. This is a precise missing connectivity-and-span step, not a claimed refutation of every possible brace argument.

Likewise, in (4) the completed a-objects have the right degrees but are not old Hamiltonian cycles on a long gap. Differences between two a_P choices are P−P'∈U, but the individual a_P may have a nonzero coset; the same holds for a_Q,a_D. Annihilating U makes their cosets fixed, not zero. The bridge is exactly their sum plus 3r+2s_arc. Proving that its coset is nonzero in an equality case still requires information about this sum. Dropping all three constants recovers an invalid short-gap analogy.

In the prism proof the additional identity P_g+Q_h=D_hg+Y pays those constants, and (12) then evaluates the sum. Neither identity has been established for an arbitrary exterior. In fact the prism identity uses the complete two-layer classification, not just the face's cyclic terminal order.

### 4.4 The quotient obstacle to transplanting J194

Put W=L+U, and set

    kappa=dim(D_G/(D_G∩W)), gamma=dim(W/(D_G∩W)).

Subtract dimensions to obtain the inherited exact identity

    Delta=kappa−gamma.                           (18)

For short gaps, V⊆W follows from the bijections and D_G⊆W+<r>. Equality Delta=1 then forces W⊂D_G and a one-dimensional quotient whose functional is 1 on every N00 displacement. Neither inclusion follows on long gaps. Even Delta=1 only says dim W=d(G)−1; it permits kappa=gamma+1 with gamma>0. Thus writing “the normalized w on D_G/W” is invalid until W⊆D_G is proved.

If G is separately known affine-full, W⊆ker A_G=D_G and gamma=0. Equality then does provide a one-dimensional quotient, but it still need not provide a constant value on N00, because V⊆W is not proved (and the I170 containment obstruction is paid). Therefore even in this additional case the short-gap 0/1 normalization cannot be assumed. The prism family has V=0 and affine fullness by its explicit rank, so it genuinely admits that normalization. These are extra properties of that family.

A conditional lower-bound certificate would be D_G⊆W+<r> (or any other one-vector extension of W); then dim D_G≤dim W+1 gives Delta≤1. More generally (18) shows the exact obligation is kappa≤gamma+1. Neither follows from the noncrossing lemma: that lemma classifies individual facial translations, whereas (18) concerns all linear combinations. I have not obtained a universal map from lost directions into within-family new directions, even allowing one missing dimension. This is the unproved step in the rank route.

### 4.5 Read source operations and unavailable interface

The actual manuscript cor:edge-avoidance (794–805) supplies one cycle avoiding a specified edge, and cor:pfaffian-paths (812–828) supplies cycles containing each three-edge path. Neither statement compares their weights or proves independence of the cycles so supplied. The actual cancellation lemma (446–483) keeps the second state fixed; the circulation lemma (497–519) CHOOSES spoke weights, which are then fixed (521 onward) to obtain nonvanishing and a forest state (through 589). No map from an arbitrary functional annihilating L0+U to those positive-circulation weights is supplied by those read statements. The Pfaffian definition (807–810) concerns orientation parity on suitable even cycles; it does not identify those signs with a rational annihilator of the present spaces. No such transport is proved here.

I178 is used only as a scope warning already contained in the read I192 record, not as an invoked theorem. Its fixed thirteen-vertex exterior, five ordered/colored ports and complete eleven-type hypotheses have not been embedded around an arbitrary four-terminal long-gap exterior. Consequently its four lifted relations cannot be substituted for generators of L0+U or constraints on beta here. I did not open its sealed infrastructure, pursue its unpaid realization questions, or reopen E183 and its dependencies.

## 5. Settled subcases, counterexample branch, and precise verdict

The complete prism family of Sections 2–3 proves BOTH clauses, including sharp equality and an independent bridge. It has just one lost old cycle, so ell=1; this is not evidence for a new general high-loss rank constraint.

The following additional elementary subcases are exact. If N00=∅ or ell=0, (1) settles exchange. If t≥ell, it also settles exchange. If |N00|=1 then D_G=L+<N−C0>, so ell≤1 and t≥ell−1; this settles only the first clause unless the bridge is independently paid. If Delta=1 and a weight annihilates L0+U but is nonzero on beta, eta=1 and exchange follows; Section 3 provides precisely such a weight for prisms. The hypothetical containment certificate in Section 4.4 settles the rank clause only, not the equality bridge. None of these conditional statements is asserted universally.

No fully specified admissible long-gap step violating either clause has been obtained. The only newly worked concrete instances form the analytically classified cap-prism family, and every one satisfies both clauses. The I168–I170 finite conclusions remain authenticated historical evidence only; no sealed computation was rerun, extended or used as a new scan. Formal vector-space arrangements with kappa≥gamma+2, or with dependent beta at Delta=1, are not graph instances and are not offered as counterexamples.

> **J195 (one precise remaining assertion, unpaid).** For every B-admissible step with k_A,k_B≥1 and N00≠∅, take the complete families, L0,U,V,c,beta of Section 1. Let epsilon=dim(L0+V+<c>)−dim(L0+V) and t=dim(L0+U)−dim L0. Then
>
> t≥dim(L0+V)−dim L0+epsilon−1,
>
> and if equality holds, beta∉L0+U.

This is a single assertion with its necessary equality clause, independent of the anchors. It is exactly the long-gap restriction of J192 because (3) identifies the right side as ell−1, and eta is zero or one. For Delta≤0 exchange is automatic; for Delta=1 it is equivalent to bridge independence; for Delta≥2 exchange fails even with eta=1. The empty-N00 branch has already been settled. The brace restriction of J195 is also unresolved.

**Original-target verdict: UNRESOLVED.** There is no decisive new constraint in the brief's sense: no structural dichotomy forcing the residual, and no verified violating instance. The exact infinite test-family proof, multi-component bookkeeping and identified failed inferences do not change that status. The prescribed stopping rule therefore applies; leave the long-gap front for parent-side parking beside the short-gap front and E183. Do not propose another short-gap or long-gap iteration here.

A future proof of both long-gap clauses would, together with the paid short-gap rank bound, reduce universal exchange exactly to the parked short-gap bridge J194/J193; it would not itself settle that bridge. Conversely a verified J195 violation would refute universal exchange at that step. Q164 (the numerical count bound) and (T), and the stronger affine-fullness goal, gain a conclusion only through the FULL exchange theorem and the appropriate already-paid reductions with their construction hypotheses; none is established here. No all-brace construction is assumed. Eight accepted findings remain the parent's program state; no substantial finding or literature novelty is nominated.

Validation is entirely the displayed degree equations, exhaustive written case splits, component tracing, coordinate identities and rational linear algebra against read, authenticated sources. Exactly the five assigned output paths were written incrementally. No research code, graph/state/matching scan, tests, experiment, replay/rebuild, source copy, snapshot, seal, further agent, ancestor/shared-ledger edit, staging, commit or publication was performed.
