# I190 analytic attempt: residual matchings, pairing and survivor control

2026-10-11. **COMPLETE WRITTEN ATTEMPT; ORIGINAL E183: UNRESOLVED.** All sixteen anchors authenticated before proof work. This unsealed record was written incrementally: hypotheses/brace deductions at checkpoint 1, pairing/sign and square-switch deductions at checkpoint 2, then the terminal-deletion paths, survivor tracing, concentration restrictions and final verdict. Section 5 states the precise remaining assertion; no proof or refutation of E183 is claimed.

## 0. Exact unchanged hypotheses and quantifier

Let X be any finite connected simple bipartite locally cubic disk. Its five distinct degree-two ports b_0,...,b_4 occur in boundary order (0,2,1,4,3), with colors (1,1,1,0,1) in label order; every other vertex is cubic. Attach b_i by e_i to the respective vertex (1,5,6,28,29) of a disjoint Y. The vertex set of Y is {1,...,11,28,29}, and its internal edges are exactly

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

Require the resulting G to be simple, planar, bipartite and a brace. Cubicity follows from the declared degrees. We use the stipulated brace consequence that every two disjoint edges of G extend to a perfect matching, together with connectedness and existence of a perfect matching. No assertion that vertex deletion preserves braceness is made.

A packing spans its side, has degree one precisely at the used ports and degree two elsewhere, and has no cycle component. Each fibre contains ALL packings of the specified used set and pairing; compatible exterior products are complete. All eleven survivor fibres are nonempty:

```
02;02  12;12  14;14  24;24
0123;02,13  0123;03,12  0134;03,14
0234;02,34  0234;03,24  1234;12,34  1234;14,23.
```

The complete lost fibres are P=(01;01) and D=(0134;01,34). The internal port-disjoint simple cycle C=(x,a,b,y,d,c,x) has chord xy. Set A={xa,by,dc}, B={ab,yd,cx}. For every such X,G,C and every admissible p in P with E(p) intersect E(C)=A and q=p symmetric-difference E(C) also in P, the original target is SOME perfect matching M of G containing A whose complement is Hamiltonian of ANY survivor local type. The packings p,q are not perfect matchings. No prescribed exterior completion, cut 2, single difference cycle, local surgery, or improvement sequence is added to the target.

The four remaining patch incidences are aa',bb',cc',dd', with distinct terminals outside C in X, possibly original ports. Color x,b,d black and a,y,c white; then a',c' are black and b',d' white. These color names are independent of the port color names above. Put R=G-V(C) and W=X-V(C). In R the four terminals have degree two and all other vertices degree three. R is balanced because G is cubic bipartite and the patch removes three vertices of each color.

Paid I188/I189 geometry supplies an empty patch disk with outgoing boundary order (a,b,d,c). Define alpha=(a'b')(c'd'), beta=(a'c')(b'd'), gamma=(a'd')(b'c'). The canonical routes K_A are a'-a-b-b' and c'-c-x-y-d-d'; K_B has routes a'-a-x-y-b-b' and c'-c-d-d'; both pair alpha. F has routes a'-a-x-c-c' and b'-b-y-d-d', pairing beta. The other Hamiltonian restrictions are the single paths L_ab,L_cd,L_bc,L_ad in I189. Gamma is impossible for two disjoint R paths by separation of alternating boundary points in the complementary disk.

For every perfect matching N of R, put D_N=E(R) minus N and H_N=D_N union E(K_A), including all four continuations. M_N=N union A is a perfect matching of G. The paid exact criterion is

    E183 on this instance iff some N has D_N cycle-free, pairing beta,
    and the canonical type satisfies
    (S): 2 in U, or 14;14, or 0134;03,14.                 (T_R)

The known q, completed by a compatible exterior in its complete P fibre, supplies such an N with beta and no cycle, but with lost type P. Thus beta existence alone is already paid; the missing intersection includes survivor type.

## 1. Source scope and brace consequences for R

### 1.1 What the actual source says

The retained main TeX was read in full (1–345, 346–595, 596–838), with focused rereading of the specified ranges. It contains no statement defining a brace or asserting two-extendability: the word 'brace' does not occur. The dual strategy (91–170) and prop:pairs (245–345) concern two edge-disjoint perfect matchings in a FACE–VERTEX INCIDENCE graph. They do not extend two prescribed edges of G or R. The brace extension consequence is instead an explicit hypothesis consequence paid by this brief and the I187 analytic Section 2/finalized review, read here. This distinction avoids importing an unread matching theorem or inventing a source lemma.

The I187-reviewed small-cut conclusions are available. Here are their relevant proofs. For a shore S of cubic bipartite G with color counts n_B,n_W and cut incidences t_B,t_W,

    3(n_B-n_W)=t_B-t_W.

A one-edge cut is impossible. A two-edge cut has one shore endpoint of each color and balanced shore. At the white endpoint choose an internal edge disjoint from the black cut edge (two distinct internal neighbors permit this). Extending these two edges forces exactly one color of crossing, contradicting shore balance. A three-edge cut has all shore ends of one color and color surplus one, so every matching crosses it once. Two disjoint cut edges would contradict two-extendability. Three pairwise intersecting edges in a simple bipartite graph share a vertex (otherwise they form a triangle). Cubicity and connectedness then force one shore to be that single vertex. Thus there is no nontrivial three-edge cut. These proofs use only the declared brace consequence.

The paid I187 deduction also gives 3-vertex-connectivity of G and the dual hypotheses, so the manuscript's main theorem, single-edge avoidance and Pfaffian-path corollary apply to G. We do not apply them to noncubic R.

### 1.2 Connectivity that really follows after deletion

**R is connected and has no bridge; in fact it has no cut vertex.** For connectedness, every component of R has at least three attachment edges to the patch, since otherwise it would give an edge cut of size one or two of G (zero contradicts connectedness of G). There are only four attachments, so there cannot be two components.

If f were a bridge of R, its two shores S,T have respectively t and 4-t attachments to the patch. In G their cut sizes are t+1 and 5-t. Both must be at least three; hence t=2 and both sizes are three. Neither shore is a singleton: a single R vertex has at most one patch attachment, since the terminals are distinct. Their complementary G shores include the patch and are also not singletons. This contradicts the exclusion of nontrivial three-edge cuts. Finally a cut vertex of a bridgeless connected subcubic graph would have at least two incident edges into each of at least two components after its deletion; otherwise one incident edge is a bridge. Four incidences exceed its degree. This proves the claim without a general connectivity theorem.

This is connectivity of R, not of every D_N. Every D_N has degree one at the four terminals and degree two elsewhere. Following edges therefore decomposes it into exactly two terminal paths and possibly k disjoint cycles, covering all vertices. Its paths pair alpha or beta, even when k>0, by the same disk separation excluding gamma. No degree or connectivity argument just given forces k=0.

A cycle component Z of D_N has all edges leaving its vertex set in N. Its shore and complementary shore in G each have more than one vertex (the latter contains C). Thus its cut has size at least four. A hypothetical residual cycle is therefore separated by at least four matching edges, not forbidden by the small-cut conclusions. Likewise, if H_N consists of two or more cycles, every component shore has at least four outgoing matching edges. This is a necessary condition, not proof that such components occur under all the hypotheses.

### 1.3 Exact limits of two-edge extension at the terminal boundary

For any PERFECT matching M of G, let J be the set of terminals whose continuation is in M. Then N=M intersect E(R) is a perfect matching of R-J. Color balance forces J to contain equal numbers of black and white terminals, so J is empty, ab,cd,ad,bc, or abcd (letters denote the corresponding primed vertices). The possible internal patch matchings are exactly:

* J empty: A, B, or {xy,ab,cd}.
* J=ab: {xy,cd} or {xc,yd}.
* J=cd: {xy,ab} or {xa,yb}.
* J=ad: {xc,yb}.
* J=bc: {xa,yd}.
* J=abcd: {xy}.

To verify completeness, remove the patch vertices matched by J. With no deletion the chord is either used (forcing ab,cd) or not (the two hexagon matchings). Removing a,b or c,d leaves a square with its two matchings; removing a,d or b,c leaves the displayed disjoint pair; removing all four leaves xy. Same-color pairs cannot balance. Conversely every listed patch matching and any perfect matching of R-J assemble to a perfect matching of G. This symbolic table concerns perfect matchings, including those with non-Hamiltonian complements; it is not restricted to I189's seven Hamiltonian rows.

Consequently, for any two disjoint requested edges f,g in R, brace extension ensures a matching of SOME R-J containing them, with J among the six sets and disjoint from their endpoints. It does not in this deduction specify J empty. In contrast, requesting aa' and cc' forces J=abcd by balance, and all four continuations together with xy occur. Hence **R-{a',b',c',d'} has a perfect matching**. For each opposite-color terminal pair I in {ab,cd,ad,bc}, requesting its two continuations yields a perfect matching of R-I OR of R-{a',b',c',d'}; it does not select the first alternative. These are existence disjunctions, not claims that all alternatives are realizable.

In any perfect matching of R exactly one of the two incident R edges at each terminal is selected and the other avoided. Both cannot be selected or both avoided. Additional simultaneous demands must respect shared endpoints. A continuation belongs to no matching N of R and is absent from every M_N=N union A. Thus a prescribed extension in G using continuations cannot silently be used as an extension in R.

### 1.4 A written exact feasibility test and the only possible forbidden-edge barrier

Here a criterion is proved, not evaluated by a search. For a finite bipartite graph L with equal class sizes, L has a perfect matching exactly when every subset S of its black class satisfies |N_L(S)|>=|S|. Necessity is injectivity of a matching. For sufficiency, choose a maximum-cardinality matching. If it misses a black vertex, follow nonmatching edges black-to-white and matching edges white-to-black from that vertex. An unmatched reachable white vertex gives an alternating path whose exchange increases the matching, impossible. All reachable whites are matched to reachable blacks; all neighbors of reachable blacks are reachable whites, and the initial unmatched black gives strictly more reachable blacks than whites. This violates the displayed inequality. Finiteness justifies the choice and tracing. This is a full elementary proof, not an invocation of an unread theorem or a computation.

In particular, a requested matching F of R edges and a forbidden edge set Z are simultaneously achievable iff F intersect Z is empty and, in

    L=(R-V(F)) minus Z,

all black subsets have at least as many neighbors. Terminal edge avoidance is included: avoiding one terminal edge forces its other edge, subject to conflicts. This criterion answers precisely which combinations can be prescribed in a particular hypothetical R; it is not a universal assertion that every conflict-free combination is possible.

There is a useful structural specialization. If f=uv (u black, v white) is in no perfect matching of R, apply the preceding proof to R-{u,v}. There is S contained in the remaining black class with |N_{R-{u,v}}(S)|<|S|. Since R has the known perfect matching N_q, |N_R(S)|>=|S|. Adding v changes this size by at most one. Therefore

    |N_R(S)|=|S|, v in T:=N_R(S), u outside S.

Conversely such a tight set forbids uv, because its |S| black vertices must use all |S| vertices of T. This is an exact certificate for a forbidden edge.

Let t_B be the number of a',c' in S, and t_W the number of b',d' in T. There are 3|S|-t_B edges between S,T. Cubic degrees in G show that the cut of U=S union T has t_B black-shore and t_B white-shore incidences, total 2t_B. U is nonempty and proper (it excludes C and u). Connectedness and absence of a two-edge cut imply t_B=2. The cut in G therefore has size four. In R there are exactly 2-t_W edges from black vertices outside S into T; these include f, so t_W<=1.

Thus **every individually forbidden R edge has a balanced tight shore containing BOTH black terminals, at most one white terminal, and precisely one or two incoming R edges; its G boundary is a four-edge cut.** Conversely a displayed tight set forbids all those incoming edges. No such shore has been constructed here, and the argument does not assert it exists in an admissible instance. It proves where failure of individual R-edge extension would have to lie. Two-edge demands may have additional residual deficiency sets in L; the single-edge certificate must not be promoted to two-extendability of R.


### 1.5 Brace-forced alternating terminal paths for EVERY R matching

Section 1.3 gives a fixed perfect matching N_0 of R-{a',b',c',d'}. For ANY perfect matching N of R, the graph N symmetric-difference N_0 has degree one at exactly the four terminals, degree zero or two elsewhere, and alternating edges. It consists of two vertex-disjoint terminal paths and possibly alternating cycles. Both ends of each path use N edges, so each path has odd length and opposite-color endpoints. Its endpoint pairing is therefore alpha or gamma; beta joins same colors and is impossible here. Planarity excludes gamma in the complementary disk. Thus these two alternating paths ALWAYS pair a'b' and c'd'. Flipping both paths deletes the four terminal matches and leaves a perfect matching of R minus those terminals; cycles can be left untouched.

This is a simultaneous two-path deletion consequence of the brace hypothesis, valid for every N, including the known beta-complement N_q. The alternating paths use BOTH N edges and complement edges. They are not the components of D_N. Their forced alpha pairing therefore does not contradict beta complements and cannot be substituted for a pairing conversion. We obtain no guarantee that these paths preserve cut edges, that they yield the four-cycle in Section 3, or that a perfect-matching-preserving recombination of them has survivor type.

## 2. Alpha versus beta: exact parity and sign information

### 2.1 Component count and matching crossings

Let k(N) count the cycle components of D_N. The two paths and the patch form two cycles for alpha and one cycle for beta, since equal pairings on four labels close separately and unequal pairings make a single four-label circuit. Thus

    components(H_N)=k(N)+2 for alpha,
                     k(N)+1 for beta.                    (1)

In particular H_N is Hamiltonian iff k(N)=0 and pairing beta. With the alternative patch F the two expressions interchange. If cycle-freeness is already known, alpha means an even canonical component count (two), beta an odd count (one). Without cycle-freeness this parity does not determine the pairing: k(N) contributes separately.

The alpha paths have opposite-color endpoints and odd edge lengths. Each has equal black and white vertex counts. The beta paths have even edge lengths, with the a'c' path having black surplus one and the b'd' path white surplus one. These statements follow by alternating colors along a path, including its endpoints; they do not exclude either pairing.

There is an exact matching-crossing formulation when k(N)=0. For one of the two path vertex sets S, write m_B,m_W for N edges leaving S at its black and white vertices. Internal N edges consume one of each color, so

    m_B-m_W=|S_B|-|S_W|.                                (2)

For alpha this difference is zero; N edges between the two paths are even in number, equally directed by color. For beta, choosing the a'c' path makes the difference one; the number of N edges between the paths is odd. In both cases these are ALL edges of R between the paths because D_N has no such edge. The G cut of S adds exactly its two patch continuations. Both shores are nontrivial, so that cut has size at least four by Section 1.1. Therefore an alpha decomposition has at least two N cross-edges, one of each direction, and a beta decomposition has at least three N cross-edges, with directional surplus one on its black-ended path. Equations (1)–(2) distinguish the cases in terms of the matching and its complement. They do not manufacture a beta matching from an alpha one.

### 2.2 Symmetric differences and what an unrestricted change permits

For two perfect matchings N,N' of R their symmetric difference is a disjoint union of even alternating cycles: each differing vertex has one edge of each matching. Conversely flipping any collection of vertex-disjoint N-alternating cycles gives a perfect matching. This permits simultaneous changes on all components; it is not an iterated improvement prescription. If Q is such a collection, then

    N'=N symmetric-difference E(Q),
    D_N'=D_N symmetric-difference E(Q).                 (3)

Deleting the D_N edges of Q cuts its paths/cycles into intervals; reinserting the N edges of Q reconnects their labelled ends. This gives an exact written test: the reconnection must have only two components with four terminal endpoints, no closed component, and endpoints beta. A matching flip alone checks degrees, not this test. N'=N_q is always an available total change, but its canonical type is P. Thus unrestricted beta reachability in the set of matchings is not the remaining issue; survivor reachability with the required topology is.

### 2.3 The Pfaffian sign cannot be an alpha/beta selector

The source defines a Pfaffian orientation at lines 807–810 and states at 825–827 that planar graphs are Pfaffian; we use these read, stipulated source assertions, not an unread external proof. Fix such an orientation of G and restrict it to R. Any even cycle Z of R whose deletion leaves a perfect matching of R also has a perfectly matchable complement in G: add A. It is therefore oddly oriented. In particular every alternating difference cycle of two R matchings has this property, since the first matching restricted off the cycle covers its complement.

Here is the sign calculation in full. Order the black and white vertices of R, and for an edge bw set s_bw=+1 for orientation black-to-white and -1 for the reverse. For matching N let pi_N be its permutation and

    tau(N)=sign(pi_N) product_{bw in N} s_bw.

On a single alternating cycle of length 2l, the permutation ratio is (-1)^(l-1), since the l matched white partners undergo one l-cycle. In a cyclic traversal exactly l edges run black-to-white and l white-to-black. Odd orientation says the product of signs relative to that traversal is -1 (the number of disagreeing edges is odd as well). Thus the product of the 2l black-to-white reference signs is (-1)^l times -1, namely (-1)^(l+1). As every edge sign is its own inverse, this product is the ratio of the edge-sign products of the two matchings. Consequently

    tau(N')/tau(N)=(-1)^(l-1)(-1)^(l+1)=1.

Multiply this equality over disjoint difference cycles to obtain the same tau for EVERY perfect matching of R. This conclusion has no condition on k(N) or alpha/beta. If a cycle-free alpha witness exists, its oriented determinant/Pfaffian matching sign agrees with that of the known beta witness N_q. A common sign supports noncancellation when counting matchings; it supplies no topological preference and no survivor type. Raw permutation signs change by (-1)^(l-1), but this depends on difference-cycle lengths, not a proved alpha/beta invariant. No Pfaffian minor identity or external matching-structure theorem is imported.

### 2.4 What the manuscript's circulation and prescribed-path operations pay

In lem:circulation (497–519), dual paths to the unbounded face assign antisymmetric spoke weights with circulation one around each bounded face. Summing boundaries shows every counterclockwise simple spoke cycle has positive weight. Lines 535–561 replace a directed edge of a D-cycle in the STATE incidence construction by its two-spoke detour. Unique black-face ownership makes this a simple isotopy, so L_+(C)-L_-(C)>0. These are cycles of the state-pair graph on dual nonroots, not components of D_N in primal R.

The proof's group product (565–589) sums ALL independent orientations of those cycles:

    product_C (-i exp(x L_+(C)) + i exp(x L_-(C))).       (4)

The leading degree is c(D), and its coefficient has common phase (-i)^c(D) times a product of positive differences. At minimum c(D) this proves nonvanishing. The fixed-second-state cancellation at 446–483 removes cyclic Q_s and recovery at 623–718 returns Hamiltonian complements. This pays the stated source result, and I188's special endpoint mark already pays a nonempty canonical image. It does not identify c(D) with k(N), with the number in (1), or with survivor type.

If a proposed survivor filter chi is a function of s alone, the fixed-s cancellation is still valid (multiplying every term of a cancelling pair by the same scalar). But the undirected-group sum becomes

    sum_{epsilon in {+,-}^c} chi_D(epsilon)
         i^{J(epsilon)} exp(x sum_C L_{epsilon_C}(C)),  (5)

and (4)'s factorization and common nonzero leading coefficient no longer follow without a proof about chi_D. A filter depending on both partners need not even respect fixed-s cancellation. No such proof for the full recovered five-port survivor condition is provided here. Positive circulation ranks the two orientations of each SOURCE cycle; reversing it changes state choices, and is not a verified surgery converting an alpha residual matching into a survivor beta residual matching.

The other requested operation is cor:pfaffian-paths, 812–828: every three-edge path in G lies in some Hamiltonian cycle, under the read hypotheses. Apply it to c-x-y-d. In such a Hamiltonian cycle x and y already have degree two, so xa and yb are absent. If cd were present, c-x-y-d-c would be a proper closed component, impossible because Y is disjoint and nonempty. Hence cc',dd' are present and cd absent. At a,b the absent xa,yb force ab,aa',bb'. The restriction is exactly K_A; the complementary matching contains A. This is a second direct proof of existence of a cycle-free beta matching, independent of choosing q. It supplies no used cut or survivor pairing. Its output may be lost P or D.

The corollary prescribes ONE path of three edges; it does not also prescribe a cut edge e_2, a remote path, or a whole exterior packing. Single-edge avoidance (794–805) similarly does not impose A along with its single edge. The dual strategy/prop:pairs do not give this joint prescription either. Thus all read source operations have a precise applicable consequence, but none here pays survivor concentration exclusion.

## 3. A controlled alpha-to-beta switch and its exact limits

Suppose N is a perfect matching of R and D_N consists of two paths P_ab,P_cd with alpha pairing and no cycle. Suppose there are distinct vertices u,u' on P_ab and v,v' on P_cd such that

    uu',vv' belong to D_N, and uv,u'v' belong to N.       (6)

These four edges form an alternating four-cycle. Define the simultaneous exchange

    N^square=(N minus {uv,u'v'}) union {uu',vv'}.

Every affected vertex loses one matching edge and gains one; N^square is perfect. Deleting uu' and vv' cuts each old path into two nonempty intervals, four in total, each containing one of the original terminals. Reinserting uv and u'v' joins intervals from different old paths, using each cut endpoint once. Thus exactly two paths remain, they span R, and there is no cycle. Each new path joins one of {a',b'} to one of {c',d'}, so its pairing is beta or gamma. Gamma is excluded by the actual planar embedding. Hence it is beta. This proves a controlled alpha-to-beta conversion; it changes four R edges and does not rely on an improvement sequence.

If the four vertices lie in W, all exchanged edges lie inside X: X is the vertex-induced side of the declared gluing and its only external incidences are e_i. Starting from the F Hamiltonian cycle D_N union F, replace F by K_A simultaneously with this square exchange. The resulting H_{N^square} is Hamiltonian and uses the SAME cut edges and the SAME Y packing. The full-type tracing in Section 4 then proves it has exactly the same survivor local type as the starting F cycle. Therefore:

    Every F survivor with a four-cycle (6) wholly in W
    yields E183 on that instance, for all eleven survivor types. (7)

This includes unbalanced F cases and type 0134;03,14, whenever (6) holds; it does not require cut 2. If (6) is not inside W, the conversion still gives beta and no residual cycle, but its type must be traced anew. It succeeds precisely when (S) holds. If only the matching crossing counts of Section 2.1 are known, the requisite endpoints need not be adjacent on both old paths. Those counts do not establish (6), and a longer curve made of several consecutive D_N edges is not an alternating cycle. No existence of (6) is asserted from braceness or fibre completeness.

**Historical checkpoint 2:** Sections 0–3 were preserved before final survivor/concentration analysis. The final verdict was still pending at this checkpoint; all successful statements above are conditional at their written scopes.

## 4. Complete survivor tracing and all settled subcases

### 4.1 How to trace any candidate, including coincident labels

For an actual candidate H_N first check k(N)=0 and beta by (1). If it fails, this particular canonical candidate is not Hamiltonian. If it passes, set U={i:e_i belongs to H_N}. Restrict D_N to W; retain every used cut incidence with its port label, and every continuation incidence with its terminal label. When a terminal is a port, keep BOTH incidence labels, including their zero-length connection if applicable. Trace the intervals in W and join the terminal labels by the actual canonical routes a'-a-b-b' and c'-c-x-y-d-d'. This produces the full pairing pi on the used port labels. A closed X component would contradict the verified global Hamiltonicity. Thus theta=(U;pi) is a genuine local packing type. Apply the exact (S), never cut membership alone when U=0134.

The paid exterior table makes this exhaustive. With 2 in U, the two-port possibilities are 02,12,24 (pairing unique), and the four-port possibilities/pairings are

    0123: 02,13 or 03,12;
    0234: 02,34 or 03,24;
    1234: 12,34 or 14,23.

All are survivors. For a two-port type an existing survivor product supplies a spanning Y path with those endpoints; any local spanning path of that same type glues to it. For the four-port sets the following paid, explicit Y packings supply both choices of exterior pairing:

* 0123 / 02,13: 1-7-6 and 5-11-10-4-3-9-8-2-29-28.
* 0123 / 03,12: 1-7-8-9-10-4-3-2-29-28 and 5-11-6.
* 0234 / 02,34: 1-7-8-2-3-9-10-4-5-11-6 and 28-29.
* 0234 / 03,24: 1-28 and 6-7-8-9-10-11-5-4-3-2-29.
* 1234 / 12,34: 5-11-6 and 28-1-7-8-9-10-4-3-2-29.
* 1234 / 14,23: 5-11-10-4-3-9-8-2-29 and 6-7-1-28.

Endpoints are port labels through the attachment map of Section 0. These are inherited I189 witnesses, not newly enumerated possibilities. For each local four-port pairing choose the OTHER exterior pairing; their union is one cycle by contraction to four labels.

Without 2, the complete paid table allows U=01,14,0134, while 04 is impossible. Type 01;01 is lost P. For U=14 the sole exterior is

    S=29-28-1-7-6-11-10-9-8-2-3-4-5,

a spanning path with port endpoints 4,1; the local type 14;14 survives. For U=0134, a local 03,14 pairing survives, completed by

    (1-7-6-11-10-9-8-2-3-4-5) and (28-29),

whose exterior pairing is 01,34. The other local pairing 01,34 is lost D. It has exterior pairing 03,14, for example (1-28) and (5-11-6-7-8-9-10-4-3-2-29). The paid complete table gives three such compatible exteriors for D. Their choice changes neither the lost local pairing nor U. This handles both no-cut-2 survivor branches explicitly.

### 4.2 Why a change inside W preserves the entire type when Hamiltonicity is restored

Suppose a starting survivor H and a resulting canonical Hamiltonian H' have identical cut edges and identical Y packing. They have the same U. With two used ports the pairing is unique. With four used ports, each X pairing is noncrossing in its disk, so only two pairings are possible; Hamiltonicity requires a pairing different from the fixed Y pairing. The other noncrossing pairing is unique, so H and H' have identical pi. Therefore theta is identical, not merely survivor status. This proves the type assertion of (7). It also applies to any L matching repair inside W once beta and absence of rest cycles have separately been established. The fact that a change is a matching repair alone does not establish those last two requirements.

### 4.3 Paid transports with their written proofs and limits

K_A already solves E183 whenever its type survives. K_B replaces its patch paths by K_A; the terminal pairing alpha, all external incidences, and W remain fixed. The same beta complement gives Hamiltonicity, and the identical labelled pairing on the patch preserves the full local type. Thus EVERY K_B survivor solves E183.

For F, D_N has two alpha paths. Replacing F by K_A with N fixed creates exactly two cycles, one through each path. Each crosses the five-edge X/Y boundary an even number of times. If either uses no cut, it is a closed X component, unaffected by exterior-only changes. A four-cut distribution (2,2) instead leaves two cycle-free X paths after removing Y. Their new pairing equals the old Y pairing, since each old Y path now closes separately. Replacing the exterior by the other pairing reconnects them. For U=0123,0234,1234 the witness list above gives that replacement and both possible local pairings survive. For U=0134 the local survivor 03,14 instead becomes 01,34, hence lost D. For U=02,12,14,24 the split is necessarily (2,0) or (0,2); for four-port sets the unbalanced alternatives are (4,0),(0,4). These give the closed-X obstruction. These are failures of a particular surgery, not of unrestricted E183. Section 3 newly settles any of these F cases that has a square (6) wholly in W.

For an L survivor, the complementary matching restricted to R misses the two unused terminals J. Comparing it with N_q gives degree one exactly at those two terminals and otherwise degree zero or two in the symmetric difference. The unique path between them alternates and begins/ends in N_q; toggling it yields a perfect matching of R. Disjoint alternating cycles may also be toggled. This pays matching degree repair, not k=0, beta or (S).

If the two unused terminals are adjacent, their connecting edge lies in the original spanning rest path (both were unmatched in its complementary matching). Moving that edge into the matching cuts the rest path into two, without a rest cycle. For L_ab this deletes c'd', so the old endpoints a',b' land in different components; the pairing is beta or gamma, hence beta. For L_cd the same argument with a'b' gives beta. Because the edge is inside X, Section 4.2 preserves the full type. For L_bc orient the original rest path b' to c': traversal of the unused edge d' then a' gives beta; a' then d' gives alpha. For L_ad orient a' to d': c' then b' gives beta; b' then c' gives alpha. The beta orders again preserve the full type. In the alpha orders, balanced (2,2) use of a four-port set containing 2 is settled by the same exterior replacement; unbalanced splits or 0134 retain the previously described obstruction. Without adjacency, or with an uncontrolled longer repair, topology and type remain open. No restriction to short repairs is imposed on E183.

## 5. Concentration exclusion: what is proved and what is still missing

Assume for analysis that an admissible instance has no canonical survivor. The exact negation of (T_R) is

    For every perfect matching N of R, if k(N)=0 and pairing is beta,
    then theta(H_N) is P or D.                           (C190)

This is a conditional hypothesis, not a constructed instance or a consistency theorem. It entails all of the following necessary constraints.

1. All eleven nonempty complete survivor fibres, with ALL compatible exterior completions, avoid K_A and K_B. They avoid balanced cut-2 F and every successful L subclass of Section 4.3. Completeness forbids ignoring an inconvenient packing or choosing only obstructed representatives.
2. Every survivor whose patch class is F has alpha complement with at least two oppositely directed matching cross-edges (Section 2.1), but admits NO alternating square (6) wholly in W. Such a square would give a same-type canonical survivor by (7), including at U=14 or U=0134. Unbalanced F may still exist as a symbolic open case; balanced 0134 F still has the lost-D exterior repair.
3. Every perfect matching N nevertheless has the pair of disjoint alpha-paired terminal-deletion alternating paths of Section 1.5. Those paths contain N edges and do not constitute D_N; flipping both produces a four-terminal-deficient matching. It has not been shown that they force the forbidden square or any other successful perfect-matching change. Ordinary two-edge extension in G has the terminal-defect alternatives of Section 1.3; it cannot be read as simultaneous extension in R with canonical routes.
4. All cycle-free beta matchings have a rigid CUT profile. Since U(P)=01 and U(D)=0134,

       N intersect {e_0,...,e_4} = {e_2,e_3,e_4} for P,
                                   {e_2} for D.          (8)

   Thus every such N contains e_2 and avoids e_0,e_1; its memberships at e_3,e_4 agree. If any beta cycle-free N avoids e_2, E183 follows. Even with e_2 present, the surviving alternatives U=14 or (0134;03,14) would also settle it. Equation (8) is a necessary concentration restriction, not a new cut-2 requirement in the target.
5. The canonical cycles supplied by q, the marked source image, and the P4 prescription c-x-y-d must all have P or D type. This is compatible with the conclusions of those EXISTENCE theorems as statements: they specify no survivor condition. It is not proof that an actual fully hypothesized graph satisfying (C190) exists. The Pfaffian sign of every R matching is constant by Section 2.3, so sign cancellation cannot by itself contradict (C190).
6. A candidate failure caused by a residual closed cycle must have at least four matching edges leaving that cycle. Any failure even of single-edge R extension has the explicit balanced four-edge-cut certificate of Section 1.4. These are additional structural demands on a proposed counterexample, not constructions of one. A matching repair could instead be feasible but yield alpha, rest cycles, or a lost beta type, without any individually forbidden R edge.

These restrictions apply to the COMPLETE fibres, not a finite sample. Fibre nonemptiness supplies Hamiltonian survivors without prescribed patch behavior. The above arguments do not force one into a settled class, nor prove the remaining concentration realizable. A mere table of allowed path patterns, a constant-sign sum over unrestricted matchings, or a collection of compatible Y witnesses is not a fully hypothesized instance. In particular there is no claim that (C190) is consistent with ALL hypotheses; consistency and its exclusion are both unestablished here.

The precise remaining assertion is:

    For every instance in Section 0, the set of perfect matchings N of R
    with k(N)=0 and pairing beta intersects the set whose canonical
    five-port trace satisfies (S).                       (R190)

Equivalently, prove that (C190) cannot hold in such an instance; or refute R190 by constructing a complete instance that verifies all hypotheses, all fibres and p,q and satisfies (C190). No fixed-root preimage or surjectivity condition is part of R190. Universal existence of the W square would be sufficient in the F case, but is neither proved nor necessary for R190. Other arbitrary rest changes remain allowed.

## 6. Three-way verdict and contribution boundary

**ORIGINAL-TARGET VERDICT: UNRESOLVED.** Sections 1–4 give the full proofs of the stated residual matching/connectivity, pairing/sign and conditional transport deductions. They do not prove R190, and no fully hypothesized refutation is supplied. The concentration step is explicitly open at the simultaneous topology/type intersection, sharpened by (6)–(8); partial beta results are not a proof of E183.

The inherited settled cases are K_A/K_B, balanced cut-2 F, the adjacent-unused-terminal L_ab/L_cd repairs, the beta traversal orders in L_bc/L_ad, and their balanced cut-2 alpha repairs. The new conditional settled case is ANY F survivor having (6) inside W; also a square elsewhere settles its instance if full tracing verifies (S). A general W-confined matching repair with cycle-free beta complement preserves the starting full type. All remaining F and L cases require a proof of unrestricted survivor-producing rest change or concentration exclusion. None is asserted globally realizable merely because it was not excluded.

All pinned OpenAI theorems are stipulated true. No upstream truth audit, external unread matching theorem, fresh literature priority result, substantial-finding nomination, acceptance-gate change, or implication for other original targets is made. Eight accepted, two remaining. The source image is nonempty at its paid scope but not claimed onto all matchings or onto survivors. The local-ear mechanism stays parked; there is no iterated improvement sequence or sequel.

Only the five assigned output paths were written, early and incrementally. File I/O, text reading and cryptographic/document integrity checking were the only computer operations used for evidence. No research code, graph/state/matching scan or test, experiment, historical replay/control rebuild, source copy, snapshot/seal, additional agent, shared-ledger edit, staging, commit or publication occurred. The parent's 23-stage replay (about 8.79 seconds), twelve facial controls and 626 matching controls remain inherited reports, not newly run evidence. Written validation is internal mathematical checking, not independent review or proof-assistant verification.
