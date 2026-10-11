# I192 — written analytic attempt

Status: COMPLETE written record, PARTIAL mathematical resolution; original-target verdict UNRESOLVED. Sections 1–8 are finalized. The five brief anchors were authenticated before any deduction. All four required reports have been read in full. This is written mathematics, not computational validation. Exact reading and failed-route limits are retained in reading-and-failures.md; this record is unsealed.

## 1. Exact scope and inherited coordinates

Let B be the finite simple undirected cubic bipartite planar 3-vertex-connected graphs with a specified plane embedding. Use exactly the admissibility of I168–I170: distinct cofacial edges e=uv and f=xy have four distinct terminals in facial cyclic order u,v,...,y,x,...; delete them and insert new vertices p,q,r,s, arms up,vq,xr,ys, and square pq,qs,sr,rp; the result H must belong to B. Put K=G−{e,f}. The requested brace steps are the brace instances of this operation, not arbitrary graph substitutions. A brace here has the usual matching meaning (every pair of disjoint edges extends to a perfect matching, in the present bipartite class). The arguments below hold on all B-admissible steps and therefore on the requested brace subclass. They do not assert that every brace has a construction all of whose intermediates are braces.

All spaces are over Q; the same dimensions hold over R. An object in a vector formula denotes its incidence vector, an edge denotes its unit vector, and diff(F) denotes the span of pairwise differences (zero for an empty or singleton family). Let d(G)=dim diff(HC(G)). Nij is the complete family of old Hamiltonian cycles having e-status i and f-status j. S=N10∪N01∪N11, L=diff(S), and d_surv=dim L. The new exterior families in K are Pux (spanning ux paths), Pvy (spanning vy paths), and D11 (spanning two-path covers paired uv and xy, with no cycle components). Set

    L0=diff(N10)+diff(N01)+diff(N11),
    U=diff(Pux)+diff(Pvy)+diff(D11),   V=diff(N00),
    ell=d(G)−dim L,                 t=dim(L+U)−dim L.

Spaces on K are embedded with zero e,f coordinates. Choose C0∈S and P∈Pux,Q∈Pvy,D∈D11, and put

    b=P+Q+D+2e+2f−3C0,
    eta=dim(L+U+<b>)−dim(L+U) ∈ {0,1}.

The pinned cor:pfaffian-paths (812–828) applies to G,H with all its finite/simple/cubic/3-connected/bipartite hypotheses and its stated planar applicability. The six paths p-r-s-q, r-p-q-s, p-q-s-r, q-p-r-s, u-p-r-x, u-p-q-v in H force respectively N10,N01,Pux,Pvy,D11,N11. For the first four, closing the new square alone is not Hamiltonian, so its two unsaturated ends must use arms. For the last two, the used p,r or p,q incidences exclude the other square edges and force the other two-arm segment. Thus all six families are nonempty. This is existence, not a statement about their affine spans.

With A10∈N10,A01∈N01,A11∈N11 define

    beta=P+Q+D+2e+2f−A10−A01−A11.

If N00 is nonempty choose N∈N00 and set

    c=N−A10−A01+A11,       r=N−C0.

The three surviving e,f signatures (1,0),(0,1),(1,1) affinely span Q². A difference with zero e,f coordinates has zero total coefficient in each of these three classes. Therefore L∩{e=f=0}=L0 and dim L=2+dim L0. As U has zero e,f coordinates, dim(L+U)=2+dim(L0+U). Both beta and c have zero degrees and zero deleted coordinates, hence lie in ker A_K (A_K is unsigned incidence). Also b−beta∈L. The fourth signature gives

    d(G)=2+dim(L0+V+<c>),
    eta=dim(L0+U+<beta>)−dim(L0+U).                 (1)

For completeness, R168's projection on child differences is (arm_up−arm_vq, square_pq−arm_xr). Transported differences have image zero and the three new classes have reference images (1,0),(−1,1),(0,−1). The square degree equations identify its zero kernel with the old degree kernel; the unique relation among the three images is their sum, whose pullback is b. Within-fibre differences pull back to L+U. Thus

    d(H)=2+dim(L+U+<b>),
    d(H)−d(G)−2=t+eta−ell.                         (2)

This also proves that changing representatives does not change the quotient bridge or its rank: the changes are in U or L. No deleted-coordinate separator is available, since the deleted-coordinate image of L is already Q².

If N00=∅, ell=0, and (2) proves exchange. No N,c,r is introduced in that case.

## 2. R170 restated without a containment assumption

Assume N00≠∅. Let A_arc be the facial u-to-x arc avoiding e,f and B_arc the v-to-y arc. Bipartiteness of the child forces opposite colors for u,x and v,y, so the arcs have lengths 2k_A+1 and 2k_B+1, k_A,k_B≥0. For an arc h0,...,h_(2k), let q=h0−h1+...+h_(2k). Put q_J=q_A,q_B,q_A+q_B for J=Pux,Pvy,D11 respectively.

F_J consists of exactly the N'∈N00 for which N'−q_J is 0/1 and has the required spanning connectivity and pairing of J. R_J={X∈J:X+q_J∉N00}. If F_J≠∅ take N_J∈F_J, X_J=N_J−q_J and E_J={X−X_J:X∈R_J}. If F_J=∅ choose any X_J∈J and set E_J={X−X_J:X∈J}. Then

    diff(J)=diff(F_J)+span E_J,
    V_good=Σ_J diff(F_J) ⊆ V,
    R=span(∪_J E_J),                U=V_good+R.     (3)

Proof: translation by q_J identifies J\R_J with F_J. Differences inside that image give diff(F_J); differences from its anchor to the remaining members give exactly E_J. If there is no image, the ordinary anchored-difference formula applies. Degree cancellation along q is necessary but not sufficient for membership: connectivity is retained in the definition.

Write

    delta_V=dim(L0+V)−dim(L0+V_good),
    delta_R=dim(L0+V_good+R)−dim(L0+V_good),
    epsilon=dim(L0+V+<c>)−dim(L0+V) ∈ {0,1}.

Subtracting (1) and dim(L+U)=2+dim(L0+U) proves

    Delta:=ell−t=delta_V+epsilon−delta_R,
    exchange ⇔ delta_R+eta ≥ delta_V+epsilon.     (4)

In particular neither V⊆U nor V⊆L+U has been assumed. Their paid failures at 431 remain intact.

## 3. Facial translation lemma: exact compatible-family classification

This is a written consequence of planarity and a single Hamiltonian cycle. It is independent of brace or affine fullness assumptions.

**Matching lemma.** Let m disjoint edges of a simple facial boundary belong to a Hamiltonian cycle N. Mark their 2m endpoints in boundary cyclic order, numbering them so the selected edges pair (0,1),(2,3),...,(2m−2,2m−1). Removing those edges from N gives m disjoint paths. Their endpoint pairing is exactly

    (1,2),(3,4),...,(2m−1,0).                     (5)

Proof. Each removed edge has distinct endpoints, so N minus the m edges is precisely m paths, with no cycle components. The paths are embedded in the closed disk complementary to the open face; a slight inward displacement of contacts with the boundary does not change their pairing. Their pairing R is noncrossing. Each R pair joins an even to an odd index, since the number of marked endpoints strictly on either side of a noncrossing chord must be even. Consider an R pair from an even i to an odd j in the forward cyclic order. The interval from i to j contains whole selected-edge pairs. Noncrossing forces every other endpoint inside that interval to be paired inside it. Hence both the selected matching and R preserve that interval. Their union is the connected cycle N after suppressing path interiors. A proper such interval is therefore impossible. Thus j is the cyclic predecessor of i, which is (5). For m=1 this is simply the path left on deleting one cycle edge. This proves the lemma, including m=2 where the contracted cycle has parallel edges.

Apply the lemma to the positively signed edges of q_A. The condition that N−q_A be 0/1 says precisely that all k_A+1 positive edges are used by N and all k_A negative edges are avoided. Each negative edge lies in a gap between successive selected edges along A_arc. By (5), its endpoints already belong to one component path of N minus the positive edges. Adding it closes that path into a cycle. Different gaps give different components. The remaining component is a ux path. Consequently, whenever the 0/1 condition holds,

    N−q_A consists of one ux path and exactly k_A cycles. (6)

The cycles are actual nonempty components: a negative edge was absent from N, and simplicity prevents the component path from being that same edge. All vertices are still covered. Thus (6) is a spanning path exactly when k_A=0. If the 0/1 condition fails it is not in Pux for that reason already. Interchanging arcs proves the Pvy version.

For q_A+q_B, choose all positively signed edges on both arcs. They are disjoint; all four terminals are distinct. Consecutive selected-edge gaps around the face consist of k_A+k_B negative arc edges and the two deleted edges e,f. Equation (5) gives one component path across every such gap. Adding the negative edges closes exactly k_A+k_B components. The two remaining paths are paired uv and xy. Therefore, whenever 0/1 holds,

    N−q_A−q_B consists of two paths paired uv,xy
    and exactly k_A+k_B cycle components.          (7)

If k_A=k_B=0, degree two at every terminal in K forces the two positive edges in every N00, so all N00 are compatible. If either k is positive, (7) or failure of 0/1 prevents membership in D11.

We have proved the complete classification

    F_Pux = N00 if k_A=0, and ∅ otherwise;
    F_Pvy = N00 if k_B=0, and ∅ otherwise;
    F_D11 = N00 if k_A=k_B=0, and ∅ otherwise.     (8)

No proper nonempty compatible-old subfamily occurs for these facial alternating-arc translations. This is stronger than just observing that some translated images are empty, but it is not an exchange inequality. It concerns the particular R170 translations; other nonlocal path operations are not excluded.

A face of a 3-connected plane graph cannot have an exterior chord between nonconsecutive boundary vertices: such a chord splits the complementary disk into two regions, each containing boundary vertices, and deleting the chord endpoints separates them. Thus, in the present class, a cross-terminal edge is exactly a one-edge complementary facial arc. This short argument also explains why a putative cross-terminal edge outside a long arc does not create an omitted case in (8).

Consequences of (8): on quadrilaterals, V_good=U=V and R=0. On a step with just one short arc, V_good=V. On a step with both arcs longer than one edge,

    V_good=0, R=U,
    delta_V=dim(L0+V)−dim L0,
    delta_R=dim(L0+U)−dim L0=t,
    ell=delta_V+epsilon.                          (9)

Thus the R170 compatible-old part provides no generators at all in the genuine long-gap case. The residual generators are all anchored differences of the actual complete new classes. This does not imply U∩V=0; shared directions can arise by linear combinations without any translated old object. Confusing absence of translated objects with disjointness of spans would be an error.

## 4. Exact long-gap bridge bookkeeping

There is an identity for every face length, but its terms must be retained. For the same N,C0 as above put

    s_arc=e+f−q_A−q_B,
    a_P=P+q_A−N, a_Q=Q+q_B−N,
    a_D=D+q_A+q_B−N.

The three a-vectors lie in ker A_K; s_arc and r lie in ker A_G. This follows because q_A has degree one at u,x and zero elsewhere, and similarly for q_B. Direct addition, with no connectivity assumption on the completed vectors, gives

    b=3r+2s_arc+a_P+a_Q+a_D.                       (10)

Changing representatives alters the sum of a-vectors only by U. Changing N by v∈V adds 3v to 3r and subtracts 3v from the sum, so (10) is invariant. The completions P+q_A and so on are degree-two vectors; they need not be 0/1 Hamiltonian cycles. Equation (8) shows that on a long arc none is an old Hamiltonian cycle. Dropping the a-terms would therefore be unsupported.

This locates exactly the failed extension of H170: a one-edge removal is a connectivity-preserving bijection, whereas the longer alternating subtraction makes isolated cycles or invalid coordinates. I178 supplies neither a bound on the span of these a-terms nor a relation to beta for a general face; its interface hypotheses must first be met (Section 6 below).

A second identity separates lost directions from genuinely new ones. Put

    D_G=diff(HC(G))=L+V+<r>,  W=L+U,
    kappa=dim(D_G/(D_G∩W)),
    gamma=dim(W/(D_G∩W)).

Then subtracting dimensions gives

    Delta=kappa−gamma,
    exchange ⇔ kappa≤gamma+eta.                   (11)

This is an exact comparison, not a claim D_G⊆W+<b>. The latter would be stronger for deficient parents. If the parent is affine-full, D_G=ker A_G, W⊆D_G, gamma=0, so the obligation becomes kappa≤eta. In that case at most one missing parent direction is allowed, and it must be recovered by the bridge. This is the induction-relevant specialization; it does not assume the universal parent fullness being sought.

## 5. Short-gap equality branch, with an actual two-factor

Suppose a=ux is an edge; reverse the roles if vy is the edge instead. Every N00 uses a by degree two at u,x; deleting a gives Pux and adding it to a spanning ux path gives one old Hamiltonian cycle. Every Q∈Pvy uses a, since u,x are internal degree-two vertices. Deleting a gives two paths; the crossing pairing is excluded by the facial disk, and the resulting pairing is uv,xy. Conversely adding a to D11 joins its two paths. These are the two H170 translation bijections. Nonemptiness gives N00≠∅. With Z=diff(Pvy),

    U=V+Z, W'=L+V+Z=L+U,
    z=Q+e+f−a−C0,
    b=r+2z modulo W',       t≥ell−1.             (12)

For the specified representatives P=N−a,D=Q−a the bridge equality is exact, not only modulo W'.

There is also an actual graph object behind z for every short-gap face: let

    F_Q=Q−a+e+f.

The two paths of Q−a have endpoint pairs uv and xy, so adding e,f closes them separately. F_Q is an actual spanning two-factor with exactly two components, and z=F_Q−C0. The statement includes hexagons and longer faces with a one-edge gap; it does not say F_Q is Hamiltonian or lies in the Hamiltonian affine hull.

If t≥ell exchange already follows. If t=ell−1, then dim W'=d(G)−1. Since D_G=L+V+<r>⊆W'+<r> and dim D_G=d(G), we have

    D_G=W'+<r>,       r∉W'.

Thus W'⊆D_G follows in this equality case; it was not assumed beforehand. If z∉D_G, then r+2z cannot belong to W', proving eta=1. If z∈D_G, write the unique quotient coefficient z=lambda r modulo W'. Equation (12) gives

    eta=0 ⇔ lambda=−1/2.                          (13)

Equivalently, normalize a functional on D_G/W' by w(r)=1. For z∈D_G the forbidden equality is w(F_Q−C0)=−1/2. It is independent of Q, since differences F_Q−F_Q' lie in Z⊆W'.

For a quadrilateral let a'=vy and s=e+f−a−a'. All three translation bijections give U=V. Taking Q=N−a' yields z=r+s and b=3r+2s. If s∉D_G exchange holds; otherwise s=alpha r modulo L+V, so lambda=1+alpha and (13) is precisely alpha=−3/2. There is no strengthened quadrilateral theorem hidden in this change of notation.

The normalized functional has values 0 on surviving cycle displacements and 1 on N00 displacements. These values do not constrain a disconnected two-factor to [0,1]. Such a constraint would require a proved convex representation or another structural theorem. The manuscript's P4 existence and single-edge avoidance assertions do not provide either. Brace matching extension concerns perfect matchings; it does not by itself identify the Hamiltonian affine hull or the value of w on F_Q. Thus no exclusion of (13) has been proved here.

## 6. What I178 does and does not transfer

I178 has a fixed thirteen-vertex exterior Y, five cut ports in a fixed cyclic order with fixed colors, and exactly eleven complete nonempty survivor product types. It does not describe the four-terminal exterior K of an arbitrary square expansion. In its notation (kept separate from the G→H notation above), choose actual local/exterior anchors x_i,y_i, global anchors c_i=x_i+y_i+chi_Ji, and A_i=c_i−c_0. With W_X,W_Y the complete within-type spaces and pi the exterior/cut projection, completeness gives

    L_5=W_X+W_Y+<A_1,...,A_10>.

The thirteen generators (three exterior differences and ten A_i) have image rank nine and four relations, with actual lifts

    K1=A6+A1−A2−A5,       K2=A8+A1−A3−A5,
    K3=A9−A1−A7,          K4=A10−A1−A4+A5−A7.

Writing an arbitrary vector as w+Gz proves exactly

    L_5∩ker pi=W_X+<K1,K2,K3,K4>.                 (14)

In particular there is no right to set K3,K4 to zero. I178's special dependence on K1,K2 and its X_i is restricted to its retained I177 graph. Actual anchor changes preserve (14); independent formal translations of fibres do not represent anchor changes.

A local functional annihilates the entire kernel in (14) exactly when it is constant with values alpha_i on each complete actual local fibre and these constants satisfy all four compatibility equations

    alpha6+alpha1−alpha2−alpha5=0,
    alpha8+alpha1−alpha3−alpha5=0,
    alpha9−alpha1−alpha7+alpha0=0,
    alpha10−alpha1−alpha4+alpha5−alpha7+alpha0=0.    (15)

These annihilate all four lifts. The two additional complete local types have residuals

    p−t_P,  d−t_D,
    t_P=x0+x2−x3+4x4−4x5,
    t_D=x2−x3+4x4−4x5+x7.                         (16)

Only with the same complete-type and ambient-image hypotheses does the span of (14),(16) equal the full-cycle projection kernel. Ambient fullness requires that span equal the ambient local kernel; it is not an implication of (15). I178's proposed two-annihilator realization is unpaid.

No deduction in Sections 3–5 supplies this five-port cut, the fixed exterior, its nine-dimensional projection, or a map sending the actual R170 residuals and beta to (16). Thus (14) cannot be substituted for L0+U in (4), and (15) does not prove a lower bound on delta_R. Even if a step has a separately verified matching interface, an explicit identification of the complete fibres and the bridge is still needed. The number four of projected relations is not a bound on a survivor codimension: the local ambient dimension and W_X vary, and the four lifts need not be independent. I178's five paid validation systems are all saturated, so their zero loss is not a deficient example.

This is the endpoint of the attempted use of I178 here. I do not investigate its unpaid two-annihilator realization or its survivor-existence descendants. E183/Z184/E182/E181/H180/L179 remain parked.

## 7. Settled subcases and retained counterexample branch

These statements are complete proofs at their scopes, not tests.

* **N00 empty, or ell=0:** t,eta≥0 in (2), so exchange holds.
* **t≥ell:** the same argument proves exchange. In R170 coordinates this is delta_R≥delta_V+epsilon.
* **Exactly one missing rank:** if Delta=1 and beta∉L0+U, eta=1 and (2) gives equality d(H)=d(G)+2.
* **Short gap:** Section 5 proves Delta≤1. Exchange follows unless z lies in D_G with coefficient −1/2 modulo W'. Every quadrilateral and hexagon has a short gap, since the positive odd arc lengths sum to face length minus two. On a hexagon their sum is four, forcing one to be one. No universal equality-case exclusion has been proved, even for these faces.
* **Quadrilateral:** U=V and Delta∈{0,1}. The only unsettled case is the coefficient alpha=−3/2 with r nonzero; if s∉D_G the bridge is independent.

For completeness the paid infinite prism subcase has an entirely written verification. Let G=C_m □ K2, m even≥4, with top/bottom edges t_i,b_i and rungs rho_i. Its Hamiltonian cycles are the m ordinary cycles C_i (all rails except t_i,b_i, plus rungs rho_i,rho_(i+1)) and X,Y (all rungs, opposite alternating rails). One exhaustion proof: if some but not all rungs are selected, each run of selected rung endpoints must have even length; the omitted rails are the unique perfect matching on each run, the same in both layers. More than one omitted rail in each layer separates the cycle into multiple components, so exactly one is omitted. With every rung selected each layer uses an alternating matching; the equal choices give disjoint squares and the two unequal choices give X,Y. With no rung selected the layers are separate cycles.

These m+2 vectors are affinely independent. In a dependence with coefficients a_i,x,y summing to zero, the top-minus-bottom equations give x=y. If S=sum a_i, each horizontal coordinate gives a_i=S+x, while S+2x=0. Thus a_i=−x and (m−2)x=0; all coefficients vanish. Hence d(G)=m+1. Coordinate comparison gives

    (m−2)(rho_0+rho_1−t_0−b_0)
       =(m−3)C_0−Σ_(j≠0) C_j+X+Y.                (17)

At the two index-0 rails its value is −(m−2), at other rails zero; at rungs 0,1 its value is m−2 and elsewhere zero. The coefficients sum to zero. If the deleted edges are rho_0,rho_1, exactly C_(m−1),C_0,C_1,X,Y survive. Affine independence gives ell=m−3,t=m−4. The lost C_j coefficients in (17) yield alpha=−(m−3)/(m−2). If the deleted edges are t_0,b_0, only C_0 is lost; ell=1,t=0 and the negated (17) gives the same alpha. Thus in both cases 3+2alpha=m/(m−2)>0, eta=1 and d(H)=d(G)+2.

These steps are admissible as in P169. A direct connectivity check is short: removing two old vertices leaves the parent's surviving old vertices connected through replacements in the intact square. Removing two new vertices leaves G−{e,f} connected (a cubic 3-connected graph has no cut of size at most two); every remaining new vertex has an old arm. Removing one old and one new vertex leaves a connected three-vertex square path attached to three terminals, or at least two if the deleted old vertex is a terminal. In the latter case the parent minus that terminal is 2-connected and deletion of the other selected edge leaves it connected. Otherwise each component of the 2-connected parent-minus-old-vertex after deleting e,f must meet at least two terminals: one would make an edge a bridge, and zero would already be disconnected. The three attachments meet all such components. Simplicity, cubicity, bipartiteness and the facial embedding are immediate from the operation. The prism itself remains connected after two vertex deletions by its intact layer or two layer paths and a surviving rung. Thus P169's infinite family is settled without any new finite run.

For ell=1, t=0 exactly when U⊆L: equivalently every survivor-constant weight is separately constant on Pux,Pvy,D11. If this fails, t≥1 and exchange holds. For quadrilaterals U=V, so t=0 exactly when all N00 cycles lie in one L-coset; otherwise t=1. Under parent affine fullness, t=1 forces W=ker A_G and eta=0, giving (1,1,0). The t=0 case becomes (1,0,1) only after proving beta independent. It must not be assumed from its frequency in historical data. Without parent fullness, eta need not vanish merely because t=ell.

**Counterexample branch.** The authenticated I168–I170 reports say every one of the 636 retained steps satisfies exchange; the ten high-loss steps are (7,6,1), and 0 and 431 are (1,0,1). They are inherited finite claims, not rerun here. In particular 431's (delta_V,delta_R,epsilon)=(1,0,0) gives Delta=1, but its eta=1 pays it exactly. Its containment failure is not a target refutation. I165's count-decreasing pair has dimensions 26 and 28, hence also satisfies the exchange equality despite a negative cycle-count gain. No fully specified failing brace step is supplied here. Formal vector patterns with beta in L0+U are not graphs and are not offered as counterexamples.

## 8. One exact remaining assertion; original-target verdict

**UNRESOLVED.** For clarity, the universal statement below is written on the full I168–I170 admissible-step class defined in Section 1; its restriction to the brace steps requested in the brief is also unresolved. No result here depends on enlarging the requested class: the unresolved equality and long-gap branches persist when brace hypotheses are imposed.

The single remaining assertion is:

> **J192 (exchange residual, unpaid).** For every admissible target step G→H with N00≠∅, put Delta=delta_V+epsilon−delta_R and take the actual complete-family beta defined in Section 1. Then Delta≤1, and if Delta=1, beta∉L0+U.

This is exactly equivalent to the original exchange inequality, not a replacement conjecture: eta∈{0,1}; if Delta≤0 exchange holds automatically; if Delta=1 it holds exactly when eta=1; if Delta≥2 it fails even when eta=1. N00=∅ is already settled. Thus the complete possible failure locus is

    Delta≥2, or (Delta=1 and beta∈L0+U).           (18)

J192 is one assertion with its necessary equality clause, not two claimed theorems. Section 3 settles the compatible-family classification, not J192. On short gaps the first clause is paid and the second reduces to (13). On both-long-gap faces, (8)–(9) remove the compatible-old generators but leave the genuine comparison t+eta≥delta_V+epsilon. Neither a rank bound nor a bridge exclusion follows just because all three residual classes are complete. The I178 relations do not bridge that gap under their present hypotheses.

There is no Q164 consequence claimed. Historically I164/I165 name Q164 as the numerical bound h(G)≥n/2+2, while the brief focuses on the stronger brace affine equality d(G)=n/2+1. Full affine dimension implies that count because a finite affine spanning set in dimension d has at least d+1 points. This distinction is retained rather than renaming either target.

Conditional arithmetic, if the missing induction is supplied: the cube (m=4 above) has d=5=8/2+1. A valid square step adds four vertices; exchange from a full parent and the degree-kernel upper bound force d(H)=d(G)+2=|V(H)|/2+1. A vertex splice has n=n1+n2−2 and the paid I165 formula gives d=d1+d2−2=n/2+1 from full pieces. A cube splice adds six vertices and adds three dimensions, also preserving fullness. Hence any established construction using these steps with exchange at every required square step preserves fullness and the numerical bound; prisms have exactly m+2=n/2+2 cycles by the above exhaustion, giving the paid tightness family. This arithmetic does not assert an all-brace construction. I165 expressly cautions against that inference. The actual external generation proofs were not reread here and are not invoked to close an induction. Since J192 remains unpaid, neither the stronger affine target nor numerical Q164 is proved or refuted.
