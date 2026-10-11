# I191: the joint concentration system

2026-10-11. **COMPLETE WRITTEN ATTEMPT; ORIGINAL E183: UNRESOLVED.** All twenty-one anchors matched before proof work. This unsealed record was initialized with explicit partial status and preserved at two partial checkpoints: Sections 0–2 first, then Sections 3–5, before final Sections 6–7. Section 6 states the single remaining joint assertion J191.

## 0. Exact hypotheses and full quantifier

X is an arbitrary finite connected simple bipartite locally cubic disk. Its five distinct degree-two ports b_0,...,b_4 have cyclic boundary order (0,2,1,4,3) and colors (1,1,1,0,1) in label order; all other vertices are cubic. The disjoint exterior Y has vertex set {1,...,11,28,29} and exactly the internal edges

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

Join b_i to vertex (1,5,6,28,29)_i by e_i. Require G to be simple, planar, bipartite and a brace, with the original meaning of brace unchanged. Its paid consequences include connectedness, perfect matchability and extension of every two disjoint G edges to a perfect matching. We do not replace braceness by these consequences or assert that R is a brace.

A packing on either side is spanning, degree one exactly at its used ports, degree two elsewhere, and has no cycle component. For each type theta=(U;pi), let F_X(theta) be the set of ALL such X packings with used labels U and endpoint pairing pi. The eleven survivor fibres are all nonempty and complete:

```
02;02  12;12  14;14  24;24
0123;02,13  0123;03,12  0134;03,14
0234;02,34  0234;03,24  1234;12,34  1234;14,23.
```

The lost fibres are the complete F_X(P), P=(01;01), and F_X(D), D=(0134;01,34); no extra nonemptiness of D is inserted. Compatible exterior products are complete: for EVERY f in any such fibre and EVERY Y packing g on the same U whose union pairing is connected, f union g union {e_i:i in U} belongs to the corresponding Hamiltonian population. For two ports connectivity is automatic; for four ports it requires different pairings. This is a Cartesian-product quantifier, not a choice of one completion per packing.

The internal port-disjoint simple cycle C=(x,a,b,y,d,c,x) has chord xy. A={xa,by,dc}, B={ab,yd,cx}. The remaining incidences are aa',bb',cc',dd', with four distinct terminals outside C in X (possibly ports). Color x,b,d black and a,y,c white; a',c' are black and b',d' white. These names need not match the numerical color names of the ports. We quantify over EVERY such instance and EVERY admissible p in F_X(P) with E(p) intersect E(C)=A and q=p symmetric-difference E(C) also in F_X(P). In particular P is nonempty. The packings p,q are not perfect matchings.

E183 asks for SOME perfect matching M of G containing A with Hamiltonian complement of ANY one of the eleven survivor types. There is no prescribed exterior, cut, source preimage, difference cycle or move sequence. Write R=G-V(C), W=X-V(C), T={a',b',c',d'}. The four terminals have R degree two; all other R vertices have degree three. R is balanced. The paid empty patch disk has outgoing order (a,b,d,c). Define alpha=(a'b')(c'd'), beta=(a'c')(b'd'), gamma=(a'd')(b'c'). Disjoint R paths cannot pair gamma in the complementary disk.

For each N in PM(R), D_N=E(R)\N consists of two terminal paths and k(N) cycles. Its terminal pairing rho(N) is alpha or beta. K_A consists of a'-a-b-b' and c'-c-x-y-d-d'. H_N=D_N union K_A is the complement of N union A in G. Let

    B_R={N in PM(R): k(N)=0 and rho(N)=beta}.

Then H_N is Hamiltonian exactly for N in B_R. Its canonical trace theta(N) is obtained by retaining all cut/continuation labels in W, including both labels and zero-length connections if a terminal is a port, and adjoining the K_A routes. The exact survivor test is

    (S)  2 in U, or theta=14;14, or theta=0134;03,14.

Thus E183 is equivalent to B_R containing an N satisfying (S). The counterexample condition is exactly

    (C190) for EVERY N in B_R, theta(N) is P or D.

The known q supplies an element of B_R of type P after any compatible completion. Existence of B_R is therefore not in doubt.

## 1. Joint constraints on one hypothetical C190 instance

All following statements refer to the SAME X,G,C,p,q; none permits separate graphs for separate fibres. The original hypotheses of Section 0 are part of the system. The following necessary consequences are paid by I190 at its reviewed scopes; proofs or explicit uses appear below.

### 1.1 Brace, defects, and universal paths

G has no one- or two-edge cut and no nontrivial three-edge cut. R is connected, bridgeless and has no cut vertex. Every cycle component of every D_N has at least four outgoing matching edges. The last assertion allows cycles separated by four or more such edges.

For every perfect matching M of G, let J record the patch continuations in M. The restriction to R perfectly matches R-J. The complete internal patch matching possibilities are:

* J empty: A, B, {xy,ab,cd}.
* J=ab: {xy,cd}, {xc,yd}; J=cd: {xy,ab}, {xa,yb}.
* J=ad: {xc,yb}; J=bc: {xa,yd}.
* J=abcd: {xy}.

Letters in J mean primed terminals. Odd J and ac,bd are impossible by balance. Two disjoint requested edges f,g in R extend in G, hence occur in a matching of SOME R-J from this table with J avoiding their endpoints. This does not force J empty. Requesting aa' and cc' forces all four continuations, hence PM(R-T) is nonempty. Requesting the two continuations of any opposite-color pair I in {ab,cd,ad,bc} gives a perfect matching of R-I OR of R-T, without selecting the former alternative. Fix N_0 in PM(R-T).

For EVERY N in PM(R), N symmetric-difference N_0 has two vertex-disjoint terminal paths Q_ab,Q_cd, of odd length, beginning and ending in N edges, together with possibly disjoint alternating cycles. Opposite endpoint colors exclude beta for these paths; the disk excludes gamma. Thus their pairing is alpha. They are alternating paths, not components of D_N. Either or both may use Y and cut edges. Nothing yet bounds their lengths or requires them to visit both D_N paths.

If a single R edge uv (u black, v white) lies in no perfect matching, I190's proved tight-set criterion supplies S in the black class, u outside S, v in V=N_R(S), |S|=|V|. The balanced shore S union V contains both black terminals and at most one white terminal and has G boundary four. This is a conditional certificate, not an assertion that any such edge exists. Residual two-edge feasibility has no stronger paid guarantee.

For every N, the canonical component count is k+2 for alpha, k+1 for beta. If k=0, the N edges between its two complement paths are even, at least two, balanced by color direction for alpha; for beta they are odd, at least three, with black-to-white surplus one from the black-ended path. All N have the same oriented Pfaffian matching sign; this does not select either topology.

### 1.2 Every survivor product must avoid every settled transport

For EVERY survivor f and compatible g, H=f union g union cut edges has one of seven patch restrictions. Besides K_A, K_B (a'-a-x-y-b-b' and c'-c-d-d') and F (a'-a-x-c-c', b'-b-y-d-d'), these are the single paths

    L_ab: a'-a-x-c-d-y-b-b';  L_cd: c'-c-x-a-b-y-d-d';
    L_bc: b'-b-a-x-y-d-c-c';  L_ad: a'-a-b-y-x-c-d-d'.

K_A,K_B require a cycle-free beta R complement. F requires a cycle-free alpha R complement. An L row requires one spanning R path between its used terminals and a complementary matching deficient at the other two terminals. The three degree-feasible isolated patch-cycle rows cannot occur because Y is nonempty.

Under C190 no survivor product is K_A or K_B. No F survivor with U containing 2 has a balanced (2,2) distribution of cut edges between its two alpha paths. No F survivor has a useful alternating square wholly in W: such a square has edges uu',vv' in D_N on different alpha paths and uv,u'v' in N. No L_ab survivor has adjacent unused c',d'; no L_cd survivor has adjacent unused a',b'. In L_bc an adjacent unused edge traversed d' then a' along the b'-to-c' spanning rest path is excluded; in L_ad, c' then b' along the a'-to-d' path is excluded. The other adjacent-edge orders produce alpha and are excluded if their canonical two-cycle cut distribution is balanced and uses 2. These are exactly the paid short repairs, not an exclusion of all L rows.

Every possible general repair of an L matching must fail at least one of cycle-freeness, beta pairing, or (S); this is C190 applied only after obtaining a perfect matching. The paid symmetric-difference repair exists, but is not guaranteed to stay in W or preserve any of these three conditions. Complete fibres forbid suppressing a packing or exterior product that satisfies a settled transport.

### 1.3 Exact exterior, profile, and existence constraints

For EVERY N in B_R,

    N intersect {e_0,...,e_4}={e_2,e_3,e_4} if theta=P,
                            ={e_2} if theta=D.          (8)

In particular e_2 is present, e_0,e_1 absent, and e_3,e_4 have equal membership. Equation (8) is necessary, not sufficient, for C190: the profile {e_2} can ALSO produce survivor local type 0134;03,14, and must have that type excluded by tracing.

For clarity, the COMPLETE no-cut-2 exterior table is literal. Put

    R1=1-28-29-2-3-4-10-9-8-7-6-11-5,
    R2=1-28-29-2-3-9-8-7-6-11-10-4-5,
    R3=1-28-29-2-8-7-6-11-10-9-3-4-5,
    S_Y=29-28-1-7-6-11-10-9-8-2-3-4-5,
    T_Y=1-7-6-11-10-9-8-2-3-4-5.

Local P has exactly R1,R2,R3 as compatible exteriors; local 14;14 has exactly S_Y; local D has exactly {1-28} together with each Ri with initial vertices 1,28 removed; local survivor 0134;03,14 has exactly T_Y together with {28-29}. The color-allowed U=04 has no admissible exterior. For U containing 2, the nine local types in Section 0 are survivors and complete compatible exteriors are included by the original quantifier; the witness list in Section 2 below is not asserted to enumerate all cut-2 exteriors.

All q completions, all cycles from the paid I188 marked image, and all cycles containing c-x-y-d must have lost type under C190. The first are specifically P; the other two populations may be P or D. Their nonemptiness does not say they exhaust B_R or include survivors. No source surjectivity is assumed.

This joint system is not claimed consistent. Keeping C190 itself in the system is essential: its necessary profile and avoidance consequences alone would be a weaker system.

## 2. Settled transports, with written reasons

K_A is already canonical. Replacing K_B by K_A preserves all four labelled terminal incidences and their alpha pairing, so preserves Hamiltonicity and the full five-port type. For F, replacing its beta patch pairing by alpha with the rest fixed closes two cycles, one along each alpha R path. Each crosses X/Y an even number of times. In an unbalanced distribution one cycle is entirely in X and cannot be removed by an exterior-only change. In distribution (2,2), deleting the exterior leaves two X paths whose pairing equals the OLD Y pairing. Replacing Y by the other pairing reconnects them to one cycle. For the cut-2 four-port sets both local pairings survive. The paid witnesses are

```
0123 / 02,13: 1-7-6 ; 5-11-10-4-3-9-8-2-29-28
0123 / 03,12: 1-7-8-9-10-4-3-2-29-28 ; 5-11-6
0234 / 02,34: 1-7-8-2-3-9-10-4-5-11-6 ; 28-29
0234 / 03,24: 1-28 ; 6-7-8-9-10-11-5-4-3-2-29
1234 / 12,34: 5-11-6 ; 28-1-7-8-9-10-4-3-2-29
1234 / 14,23: 5-11-10-4-3-9-8-2-29 ; 6-7-1-28.
```

Each displayed pair covers the thirteen Y vertices disjointly; the literal consecutive edges are declared in Section 0. Choosing a pairing different from the new X pairing gives one cycle. For U=0134 the same balanced operation changes survivor local 03,14 to lost local 01,34; using any of its three compatible exteriors cannot change the local type. This is a failed operation, not a counterexample.

For L, let N_H match R except at unused terminals J'. Its symmetric difference with N_q has exactly one path with those endpoints, beginning and ending in N_q. Toggling that path repairs both deficits; all other vertices retain one matching edge. If J' are adjacent, their connecting edge is in the original spanning rest path, and adding it to N_H cuts that path into two, with no cycle. For L_ab or L_cd the old two endpoints land in different new components, giving beta or gamma; planarity forbids gamma. The traversal orders of the mixed rows in Section 1.2 give beta by directly reading the two new endpoint pairs. The reverse orders give alpha, to which the balanced cut-2 repair applies. A longer repair has no such proved topology guarantee.

Any repair wholly in W that does yield a cycle-free beta complement preserves the starting full type: cut set and Y packing stay fixed, and the unique noncrossing X pairing different from a fixed four-port Y pairing stays the same (two-port pairing is unique).

For the useful square, remove uu',vv' from the two alpha paths. Four intervals remain, each with one original terminal. Adding uv,u'v' joins intervals from different old paths, uses each cut endpoint once, and leaves exactly two spanning paths without a cycle. Pairing is beta or gamma; planarity forces beta. Thus N^square=(N\{uv,u'v'}) union {uu',vv'} is perfect and belongs to B_R. If the square is in W, installing K_A simultaneously leaves cut set and Y packing fixed, so the preceding type argument proves E183. Universal existence of such a square has not been established.

## 3. The universal alpha paths: exact reconnection audit

Fix an F survivor H and its residual perfect matching N. Write P_ab,P_cd for D_N's two alpha paths. These span R and have equal black/white counts individually. Let E_cross be the N edges between their vertex sets. Internal matching edges consume equal color counts, so E_cross has equally many black-to-white and white-to-black incidences on P_ab, at least one of each. The lower bound uses the nontrivial G cut consisting of E_cross and the two patch continuations. It does not assert that the endpoints of one edge of each direction are adjacent on either path.

Compare this PARTICULAR N with the fixed N_0 of Section 1.1. Orient Q_ab from black a' to white b' and Q_cd from black c' to white d'. Each N edge on either alternating path is then traversed black to white; each intervening N_0 edge is traversed white to black. Every N_0 edge on a difference path is outside N, hence in D_N. It stays on a single P path. Consequently the ONLY switches between P_ab and P_cd along Q are N cross-edges. Each Q has both endpoints on the same P path, so it switches an even number of times, using equally many cross-edges in each direction. The two Q's are vertex-disjoint, so no cross-edge is reused. The unused E_cross edges also balance by direction, by subtraction from the full balance.

This sharpens the minimum two-cross-edge case: if |E_cross|=2, either neither edge lies on Q_ab union Q_cd, or BOTH lie on one Q and the other Q uses neither. One cross-edge on each Q is impossible, since each would then finish on the wrong P path. Both allowed alternatives still leave the actual locations and intervening path lengths unspecified. In particular, no equation above says the endpoints are consecutive on BOTH P paths, as a useful square requires. This is a consequence for actual hypothetical instances, not an assertion that each alternative is realizable under all hypotheses.

The same calculation on any N in B_R is different but compatible. Its black-ended path P_ac and white-ended path P_bd have color surplus +1 and -1. Both oriented deletion paths start on P_ac and end on P_bd, hence each uses one more cross-edge from P_ac to P_bd than in reverse. Their disjoint union uses surplus TWO, while the whole N cross set has surplus ONE. The unused cross-edges therefore have surplus MINUS ONE. At least one unused reverse cross-edge must exist; if there are exactly three cross-edges, the paths use exactly two forward ones and leave the single reverse one unused. This independently recovers the paid lower bound three and describes how universal alpha deletion paths coexist with a beta complement. It is not a contradiction to beta or to lost beta profiles.

Why the immediate reconnection lever fails: flipping an entire Q removes the terminal matching edge at each endpoint and gives no replacement there. It produces a matching deficient at that terminal pair. Flipping both Q's leaves all four terminals deficient. Moreover, within the union of these two disjoint paths alone, no nonempty subset can be flipped while keeping N perfect: at each internal vertex membership of the preceding flipped edge forces membership of the next; this propagates to a terminal, where a flipped edge would leave its matching degree zero. Thus this path-only method cannot yield a DIFFERENT perfect matching of R. Disjoint alternating CYCLES in N symmetric-difference N_0 may be flipped, but the theorem neither ensures their presence nor controls their complement reconnection. A new attachment of the path ends would need additional edges and a proof of coverage/pairing/type. No such attachment follows from the two paths' existence.

For any two perfect matchings N,N', their symmetric difference consists of alternating cycles, because every differing vertex has degree two with one edge of each matching. Conversely an alternating cycle collection can be toggled. The exact success condition is obtained by removing its D_N edges, tracing all resulting intervals, and adding its N edges: exactly two spanning paths, beta endpoints, no closed component, and (S) after canonical tracing. This is a mathematical criterion, not a requested scan. N'=N_q is available but lost. The universal deletion paths supply no proof of this joint condition. We have refuted the particular inference that simply flipping the guaranteed paths preserves perfectness; we have NOT refuted the possible theorem that the full joint hypotheses force some other successful reconnection.

## 4. Fixed-Y improvement: every useful square on an F survivor succeeds

**Proposition (conditional transport, all of R).** For ANY Hamiltonian F survivor in an exact Section 0 instance, a useful alternating square as in Section 2 anywhere in R yields a canonical survivor, possibly of a different survivor type. Hence C190 excludes useful squares anywhere in R for EVERY F survivor and EVERY compatible exterior completion.

The pairing/cycle-freeness proof is already given in Section 2 and does not use the location of the square. What remains is a complete type proof. Every square of R either lies in W, lies in Y, or crosses the five-edge cut. Because the cut edges have pairwise disjoint endpoints, a square cannot have four cut edges; each vertex would need two. A crossing square has exactly two cut edges, an edge joining their X endpoints, and an edge joining their Y endpoints. Among the five Y port vertices {1,5,6,28,29}, the ONLY internal adjacencies are 1-28 and 28-29, by the literal edge list. Thus a crossing square uses precisely {e_0,e_3} or {e_3,e_4}. In particular NO square contains e_2. This classification remains true when a port is a patch terminal: that port is in W, and C is port-disjoint.

If the F survivor uses cut 2, then e_2 is absent from N and remains absent from N^square. The canonical Hamiltonian cycle still uses cut 2, so it survives by (S), regardless of all other type changes. If the square is in W, Section 2 already proves full-type preservation for every type. It remains to consider a square in Y or crossing the cut for each of the two no-cut-2 survivor types.

**Starting type 14;14.** Its Y packing is uniquely S_Y. All thirteen Y vertices lie on a single D_N alpha path, since S_Y is one connected spanning Y path. A useful square requires one D_N edge on EACH alpha path, so cannot lie wholly in Y. The matching cut profile is {e_0,e_2,e_3}. In an alternating crossing square the two cut edges are opposite, hence both in N or both in D_N. The pair {e_3,e_4} is mixed and impossible. For {e_0,e_3}, both cut edges are in N, and the two internal square edges are b_0b_3 and 1-28 in D_N. Toggling removes e_0,e_3 from N and adds those internal edges. The new used set is 0134. Its Y packing is S_Y with 1-28 removed, namely T_Y and 28-29, of pairing 01,34. The new canonical cycle is Hamiltonian by the square proof, so its X pairing must be 03,14. This is the survivor 0134;03,14. This conclusion is conditional on the square being useful; a crossing alternating square whose complement edges are on the SAME alpha path is not covered.

**Starting type 0134;03,14.** Its Y packing is uniquely T_Y together with 28-29. If these two Y components lie on one alpha path, no square wholly in Y is useful. If they lie on different alpha paths, a useful square wholly in Y would have to use 28-29 as one of its D_N edges. But there is no four-cycle of Y containing 28-29: the only other Y neighbor of 28 is 1, the only other Y neighbor of 29 is 2, and 1-2 is absent. Thus again no useful square lies wholly in Y.

Here N's cut profile is {e_2}, so all of e_0,e_3,e_4 are in D_N. A crossing alternating square on {e_3,e_4} would need the internal edge 28-29 to be in N, whereas it is in the stated Y packing, hence in D_N. It is therefore impossible. A crossing square on {e_0,e_3}, if useful, has internal edges b_0b_3 and 1-28 in N. Toggling inserts e_0,e_3 into N, producing cut profile {e_0,e_2,e_3}, used set 14. The exterior gains 1-28, turning T_Y together with 28-29 into S_Y. The canonical Hamiltonian cycle thus has type 14;14 and survives. These cases exhaust the no-cut-2 survivor possibilities and prove the proposition.

This is a strict extension of the paid sufficient condition's location scope: it eliminates the need to keep the square in W. No claim is made that the newly allowed crossing-square cases are realized in some admissible instance, or that a useful square must exist in every instance. The existence gap persists even for an F survivor; a counterexample's survivors may instead all lie in L rows. Consequently this strengthened exclusion is not a decisive concentration contradiction.

## 5. Exterior saturation, cut counts, and the sign-counting lever

### 5.1 The common e_2 profile cannot be promoted to all matchings

Let color 1 denote the four-port color and color 0 the single-port color. Counting degrees in X gives

    3(|X_1|-|X_0|)=4-1=3.

Deleting C and then T removes equal numbers of both colors. Thus W and W-T have surplus one in color 1. In ANY perfect matching of R, and also in ANY perfect matching of R-T, internal matching edges pair opposite colors, so if z_i indicates selection of cut edge e_i,

    z_0+z_1+z_2+z_4-z_3=1.                         (9)

When a terminal is a port and deleted, its cut indicator is zero; the same equation applies. With z_3=0, exactly one other cut edge is selected; with z_3=1, exactly two other cut edges are selected. This yields ten formal profiles: {e_j} for j in {0,1,2,4}, or {e_3,e_j,e_l} with distinct j,l in {0,1,2,4}. It is a necessary degree list, not a realizability assertion. The C190 profiles are two of these ten. The identity does not force the other eight profiles to occur in B_R, even if some occur among arbitrary residual matchings.

Under C190, any residual perfect matching with a profile outside the two in (8) MUST have k>0 or rho=alpha. With profile {e_2}, even beta and k=0 must additionally trace as D, not the surviving 0134 pairing. Universal alpha deletion paths apply to all these matchings but neither change (9) into (S) nor keep the result perfect when toggled.

The read source's cor:edge-avoidance and cor:pfaffian-paths give one-edge avoidance and ONE prescribed three-edge path, respectively, in G. The path c-x-y-d forces K_A: x,y then omit xa,yb, while using cd would close the proper four-cycle c-x-y-d-c; hence cc',dd',ab,aa',bb' are forced. This supplies B_R but no cut prescription. Applying the corollary to a remote path, or asking separately for an edge avoidance, supplies another Hamiltonian cycle without a proved K_A restriction. These separate existential statements cannot be conjoined. The source's two incidence-state matchings are likewise not two requested residual edges. No contradiction of (8) is obtained this way.

### 5.2 Completeness gives an exact multiplicity constraint

Let c_P and c_D be the numbers of local X packings of types P and D whose patch restriction is exactly K_A. These are nonnegative integers, and c_P>=1 because q is such a packing. For any fixed local canonical packing, compatible exterior products are all present and have the same patch restriction. Each P packing has exactly the three exteriors R1,R2,R3; each D packing has exactly the three tail exteriors of Section 1.3. Each resulting Hamiltonian cycle gives a distinct residual matching N. Conversely any N in B_R determines its local packing and exterior uniquely. Therefore, under C190,

    |B_R|=3(c_P+c_D),
    sum_{N in B_R} product_{e_i in N} z_i
       =3c_P z_2 z_3 z_4 + 3c_D z_2.                (10)

The product here is ONLY over the five cut edges. This is a proved counting and cut-generating-polynomial identity for actual hypothetical instances, with |B_R| at least three and divisible by three. It uses complete exterior products, not a sampled witness table. It does not assert c_D>0. It is stronger than the support statement (8) as counting information, but does not bound either coefficient from above.

For a general type theta let f_theta be the number of X packings having patch F, and y_theta the number of compatible Y packings. Patch restriction is fixed by X alone. Different f,g products give different Hamiltonian F cycles, and each F cycle determines a unique cycle-free alpha matching of R. Conversely every such alpha matching yields a Hamiltonian F cycle. Thus the number of cycle-free alpha matchings is the sum of f_theta y_theta over all compatible types (the eleven survivors and P,D, by the paid exterior possibilities). In particular y_P=y_D=3 and y_14=y_(0134;03,14)=1. The nine cut-2 values are positive, but their exact multiplicities are not evaluated here or needed. Nonempty survivor fibres need not have f_theta>0: their members may have L restrictions. Nor does fibre nonemptiness force c_theta>0 for any survivor.

This states precisely what completeness does and does not count. It forbids deleting any successful product, but supplies no proved numerical relation forcing one of the canonical-survivor coefficients to be positive.

### 5.3 Constant Pfaffian sign does not compare the topology populations

Fix the read Pfaffian orientation of G and restrict it to R. For ordered black/white vertices let tau(N)=sign(pi_N) times the product of oriented edge signs of N. On an alternating difference cycle of length 2l, adding A to the outside matching proves the cycle has a perfectly matchable complement in G, hence is oddly oriented. Its edge-sign ratio is (-1)^(l+1), while the permutation ratio is (-1)^(l-1). Their product is +1. Taking the product over all disjoint difference cycles proves tau(N)=tau_0 for every N, independent of k and rho.

Let A_R be the cycle-free alpha population and C_R the residual matchings with k>0. These and B_R partition PM(R). Expanding the signed bipartite adjacency determinant directly over permutations and giving each cut edge variable z_i yields

    tau_0 det K_R(z)= A(z)+B(z)+C(z),                 (11)

where each polynomial is the sum of cut monomials of its population. This identity is simply the determinant definition and the proved common sign; no external determinant theorem is invoked. All coefficients on the right are nonnegative counts. Under C190 insert (10) for B(z). Equation (11) supplies neither a negative term to cancel the lost population nor an equality between A(z) and B(z). In particular it does not contradict B(z) being divisible by 3 or supported on the two lost profiles. This refutes the proposed cancellation/sign-selection inference, not all possible uses of further (unproved) relations among minors.

The source's positive circulation is on SPOKE cycles of paired dual states (lem:circulation, lines 485–561). Its orientation-group product at 565–589 has a common leading phase only after summing every independent orientation in the group. Restricting to recovered survivors inserts an indicator depending on those orientations; the product factorization and positive leading magnitude are not established for that restriction. Fixed-second-state cancellation at 446–483 remains valid for an indicator of that state, but does not establish nonvanishing. Source-cycle count is not identified with k(N) or the alpha/beta population sizes. Hence that read operation supplies no missing relation for (11).

Historical checkpoint 2: Sections 3–5 and the all-R conditional square transport have now been written. No contradiction of the entire joint system and no fully hypothesized instance have yet been established; the final disposition remains pending at this checkpoint.

## 6. Construction branch and the precise remaining joint assertion

No concrete X satisfying C190 has been constructed. The symbolic construction branch exposes the following necessary simultaneous choices. One must choose a SINGLE finite disk X with the stated colored ports and a brace completion, and one p,q pair of the exact lost type. For each of the eleven survivor types one must supply a nonempty COMPLETE fibre, so specifying eleven hand-picked routes is insufficient; every additional packing and every compatible Y completion must obey the exclusions. Every F survivor must be unbalanced when it uses cut 2 and must avoid useful squares everywhere in R by Section 4. Every L survivor must avoid its successful short repairs; all of its unrestricted perfect-matching repairs must fail topology or survival. Meanwhile PM(R-T) must be nonempty, every residual perfect matching must carry the universal deletion paths, every residual complement cycle must meet the four-edge shore bound, and the entire nonempty B_R must have precisely the lost support and triple multiplicities (8),(10), with profile {e_2} always traced as D.

Merely drawing two paths with balanced cross-edges and no useful square would verify none of brace extension, simultaneous realization of the eleven fibres, or the universal statement over B_R. Similarly, choosing formal nonnegative values for c_P,c_D,f_theta consistent with (10),(11) realizes only numbers, not a graph. These partial patterns have not been promoted to an instance. In particular the proof does not establish that all-F concentration, all-L concentration, or any particular mixture is consistent under the exact hypotheses. No graph was generated or scanned in this attempt.

Here is ONE precise remaining assertion, with the full joint system inside its quantifier:

> **(J191)** There does not exist an instance (X,Y,G,C,p,q) satisfying every hypothesis and complete-fibre/product quantifier of Section 0 for which (i) every N in the nonempty B_R has theta(N) in {P,D}, hence the cut polynomial (10) with c_P>=1; (ii) every product of each of the eleven complete survivor fibres with every compatible exterior avoids K_A,K_B, balanced cut-2 F, all successful short-repair L cases, and every useful F square anywhere in R; and (iii) the SAME R satisfies the brace-derived cut/defect constraints, a fixed N_0 in PM(R-T) and its universal alpha deletion-path constraints of Sections 1 and 3.

The statement includes the actual type requirement in (i), not just its weaker cut profile. The remaining task is to prove J191 or exhibit an actual instance violating it with all hypotheses verified. By the deductions above, C190 plus Section 0 implies (ii),(iii) and (10); conversely (i) is C190. Thus J191 is exactly equivalent to E183, with no change to its original quantifier. This attempt neither proves J191 nor realizes its negation. The unmet joint constraint is whether universal alternating path/brace structure and all complete survivor products can coexist with exclusive LOST support of ALL cycle-free beta complements; the all-R square exclusion and triple multiplicity sharpen its necessary form without deciding it.

## 7. Verdict, proof limits, and stopping boundary

**ORIGINAL-TARGET VERDICT: UNRESOLVED.** No complete E183 implication chain and no fully hypothesized refutation are claimed. All settled subcases used here have written proofs in Sections 2 and 4. Section 3 proves the alternating-deletion crossing constraints and exact failure of path-only flipping. Section 5 proves the degree-profile list, triple multiplicity, and constant-sign counting formula at their stated scopes. The universal square-existence or more general simultaneous topology-and-type reconnection needed for J191 remains unproved.

The all-R square result is conditional transport, not a decisive new constraint resolving concentration. The coefficient divisibility and path-crossing constraints are necessary bookkeeping/structure, not an inconsistency or consistency theorem. No substantial finding is nominated; the parent decides acceptance. Eight accepted, two remaining. The brief's stopping rule therefore applies to this UNRESOLVED final focused attempt: this record supplies no basis to keep the E183 line open contrary to the parent's stated parking rule. The record itself makes no shared-ledger edit or new research dispatch. The local-ear mechanism stays parked; there is no iterated improvement sequence.

All upstream OpenAI results at the stipulated revision are accepted as true. Full actual source operations, scopes and gaps are documented in the companion reading/literature files. The arguments use the paid I190 deductions and elementary written counting, path tracing and determinant expansion; no external theorem is invoked unread. No source-image surjectivity, fixed-root survivor nonvanishing, external priority claim or implication for another original target is asserted.

Only the five assigned files were written, with early explicit partial initialization and two incremental checkpoints. The only computation used was administrative file I/O, text inspection, JSON and SHA-256 authentication/document checks. No research code, graph/state/matching scan or test, experiment, historical replay/control rebuild, source copy, snapshot/seal, agent, staging, commit, publication or ancestor/shared-ledger edit was performed. Parent-reported finite checks (23 stages in about 8.69 seconds, twelve facial and 626 matching controls) were not rerun. This is internal written verification, not independent review or proof-assistant certification. Output hashes are detached.
