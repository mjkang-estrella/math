# I192 — the universal exchange residual

Status: COMPLETE written assignment, PARTIAL mathematical resolution. **Original-target verdict: UNRESOLVED.** This is an unsealed proof-only record. No substantial finding is nominated; acceptance remains with the parent.

The written analysis proves an exact classification of R170's compatible facial-translation families and gives the short-gap bridge an actual two-component two-factor interpretation. Neither excludes the remaining bridge cancellation or supplies the long-gap rank inequality. No counterexample step is claimed.

Full deductions, including all coefficients, source hypotheses, settled subcases and the prism proof, are in [analytic-attempt.md](../experiments/i192_exchange_residual/analytic-attempt.md). Failed routes and exact reading limits are in [reading-and-failures.md](../experiments/i192_exchange_residual/reading-and-failures.md). The files were created with PARTIAL status before proof work and updated incrementally.

## 1. Authentication and exact domain

All five required detached SHA-256 anchors matched before proof work:

* I168: `696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31`.
* I169: `1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf`.
* I170: `8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096`.
* I178: `77bbc27865e326b5b5e2eebd52f61437683b260feb82c6ed811b14216c2bdc78`.
* Retained manuscript: `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.

The brief, all four finalized parent dispositions, I191's parking disposition and every additional actual input are bound in [input-authentication.json](../experiments/i192_exchange_residual/input-authentication.json). This authenticates report bytes, not a fresh certificate replay. The four required reports were read in full before new deduction. All stipulated OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted as true.

The exact ambient quantifier is I168–I170's: G and H are finite simple undirected cubic bipartite planar 3-vertex-connected graphs with the specified plane embedding; e=uv and f=xy are disjoint facial edges with terminal order u,v,...,y,x,...; H replaces them by arms up,vq,xr,ys and square pq,qs,sr,rp on four new vertices, and is again in that class. K=G−{e,f}. Every result below holds for this full admissible-step class, and therefore for its brace steps. Imposing that G and H are braces (every two disjoint edges extend to a perfect matching in this bipartite class) gives the brace-only restriction, which also remains unresolved. No claim that every brace admits an all-brace construction is assumed.

## 2. Exact residual and symbols

All spaces are over Q (equivalently R). Write diff(F) for pairwise incidence-vector differences, zero for an empty or singleton family. Let Nij be the complete old Hamiltonian-cycle family with e,f usage i,j, S=N10∪N01∪N11, d(G)=dim diff(HC(G)), and

    L=diff(S),  L0=diff(N10)+diff(N01)+diff(N11),
    V=diff(N00),
    U=diff(Pux)+diff(Pvy)+diff(D11),
    ell=d(G)−dim L,       t=dim(L+U)−dim L.

Pux,Pvy are spanning paths in K with those endpoints; D11 consists of spanning two-path covers paired uv and xy, without cycle components. All six surviving/new classes are nonempty by the actual manuscript P4 corollary, lines 812–828, through the six explicit child paths proved in the analytic attempt.

Choose C0∈S, P∈Pux,Q∈Pvy,D∈D11. Edges in vector expressions denote unit vectors. Then

    b=P+Q+D+2e+2f−3C0,
    eta=dim(L+U+<b>)−dim(L+U) ∈ {0,1}.

R168's two-dimensional child projection gives

    d(H)=2+dim(L+U+<b>),
    d(H)−d(G)−2=t+eta−ell.                         (1)

With A10∈N10,A01∈N01,A11∈N11 put beta=P+Q+D+2e+2f−A10−A01−A11. If N00≠∅ choose N∈N00 and put c=N−A10−A01+A11 and r=N−C0. The three surviving deleted-edge signatures span Q², so

    dim L=2+dim L0,
    d(G)=2+dim(L0+V+<c>),
    eta=dim(L0+U+<beta>)−dim(L0+U).                (2)

Beta,c belong to ker A_K and b−beta∈L. These are exact offsets, not within-class-only replacements.

For the odd complementary arcs A_arc,B_arc, let q_A,q_B be alternating edge sums starting and ending with +1. Use q_J=q_A,q_B,q_A+q_B for J=Pux,Pvy,D11. R170's compatible family F_J consists exactly of old N' such that N'−q_J is a 0/1 object of J. Its residual class is R_J={X∈J:X+q_J∉N00}. Choose a translated anchor if F_J is nonempty and let E_J be residual-minus-anchor differences; if F_J is empty use all anchored differences of J. Then

    diff(J)=diff(F_J)+span E_J,
    V_good=Σ diff(F_J),  R=span(∪E_J),  U=V_good+R,
    delta_V=dim(L0+V)−dim(L0+V_good),
    delta_R=dim(L0+V_good+R)−dim(L0+V_good),
    epsilon=dim(L0+V+<c>)−dim(L0+V) ∈ {0,1},
    Delta:=ell−t=delta_V+epsilon−delta_R.          (3)

Thus exchange is exactly delta_R+eta≥delta_V+epsilon. If N00 is empty no N-anchor is used: ell=0 and exchange follows from (1).

## 3. The exact obstruction to longer facial translations

Write the arc lengths as 2k_A+1 and 2k_B+1. The following is proved in writing, without new graph data:

    F_Pux=N00 if k_A=0, and ∅ otherwise;
    F_Pvy=N00 if k_B=0, and ∅ otherwise;
    F_D11=N00 if k_A=k_B=0, and ∅ otherwise.        (4)

Here is the essential proof. Select m disjoint facial edges of one Hamiltonian cycle and label their endpoints cyclically as (0,1),(2,3),... . Deleting them leaves m paths with a noncrossing endpoint matching in the complementary disk. A matching chord from an even endpoint to an odd endpoint bounds an interval consisting of whole selected-edge pairs. If that interval were proper, both matchings would preserve it and their union would not be the single original cycle. Hence the path matching must pair (1,2),(3,4),...,(2m−1,0).

If N−q_A is 0/1, N uses every positive arc edge and avoids every negative one. Deleting the positive edges leaves exactly the paths just described. Every negative edge closes its own gap path into a cycle, leaving one ux path and exactly k_A isolated cycles. If 0/1 fails, membership already fails. The two-arc operation similarly leaves uv and xy paths and exactly k_A+k_B cycles. Terminal degree two forces the positive one-edge arcs whenever k=0. This proves every case in (4). The full proof handles m=1,2, the disk pairing and all degree conditions explicitly.

A cross-terminal edge in this 3-connected plane setting is a one-edge facial arc: a chord between nonconsecutive face vertices would separate the complementary disk and make its two endpoints a vertex cut. Thus (4) covers the H170 short-edge cases without an extra chord exception.

Consequently V_good=V on a short gap, while on two genuinely long gaps

    V_good=0, R=U, delta_R=t,
    delta_V=dim(L0+V)−dim L0, ell=delta_V+epsilon. (5)

The absence of translated old objects does not imply U∩V=0. Recovering directions by other linear combinations is precisely what remains at issue. This classification is a simplification of the bookkeeping, not a lower bound on t.

For any arc lengths the correct bridge extension is

    s_arc=e+f−q_A−q_B,
    a_P=P+q_A−N, a_Q=Q+q_B−N,
    a_D=D+q_A+q_B−N,
    b=3r+2s_arc+a_P+a_Q+a_D.                       (6)

Degree cancellation and direct addition prove (6). The a-terms cannot be discarded: their completed objects are not old Hamiltonian cycles on long arcs. This is the precise failure of extending H170 by treating an alternating arc as a single edge.

## 4. Equality-case branch and I178 limit

If a=ux is an edge, the exact bijections N→N−a from N00 to Pux and Q→Q−a from Pvy to D11 give, with Z=diff(Pvy),

    U=V+Z, W'=L+V+Z=L+U,
    z=Q+e+f−a−C0,
    b=r+2z modulo W',     t≥ell−1.                (7)

All r,z,Z notation is confined to this short-gap formula as in H170. The translated cover Q−a has uv,xy pairing, so

    F_Q=Q−a+e+f

is an actual spanning two-factor with exactly two components, and z=F_Q−C0. This interpretation applies to all short gaps, including hexagons.

In the equality case t=ell−1, the parent difference space D_G equals W'+<r>, with r nonzero modulo W'. If z∉D_G the bridge is independent and exchange holds. Otherwise z=lambda r modulo W', and failure is exactly lambda=−1/2. On a quadrilateral s=e+f−ux−vy gives z=r+s, so this is the paid S169 failure alpha=−3/2 for s=alpha r. No brace-specific argument here excludes either value. A normalized weight on the Hamiltonian fibres need not have its value on a disconnected two-factor between its values on those fibres; that missing bound cannot be assumed.

I178's four actual lifted relations remain

    K1=A6+A1−A2−A5, K2=A8+A1−A3−A5,
    K3=A9−A1−A7, K4=A10−A1−A4+A5−A7.

They describe the entire survivor projection kernel only under its fixed thirteen-vertex exterior, five ordered/colored ports and complete eleven-type hypotheses. The report gives no identification of that interface with an arbitrary four-terminal step's U,R or beta. Its two extra local completion residuals require a separate fullness/separation condition. Counting the four relations therefore supplies no bound on Delta and no bridge exclusion. The analytic attempt states all four functional equations and both completion targets, with the anchor and completeness restrictions retained. The E183 line and its predecessors remain parked; no realization problem on that line was reopened.

## 5. Settled cases and counterexample status

Exchange is proved whenever ell=0, whenever t≥ell, and whenever Delta=1 with beta independent of L0+U, directly from (1)–(3). Every short-gap step has Delta≤1. Every quadrilateral or hexagon has a short gap by the positive odd-arc length count. The equality bridge remains the unsolved case even there.

The paid infinite family is retained with a full written proof: for every even prism C_m □ K2 and either opposite-edge deletion on a lateral square, alpha=−(m−3)/(m−2) and 3+2alpha=m/(m−2)>0. Adjacent-rung deletion gives (ell,t,eta)=(m−3,m−4,1); rail deletion gives (1,0,1). The analytic attempt proves exhaustion, affine independence, the coordinate identity and admissibility, without running finite checks.

For ell=1, t=0 exactly when U⊆L, equivalently every survivor-constant weight is constant separately on the three new classes. On quadrilaterals this says all N00 cycles occupy a single L-coset. Otherwise t=1 there; with an affine-full parent eta=0, giving (1,1,0). The bridge-only case (1,0,1) requires the independent bridge and is not automatic.

No certified counterexample to exchange emerges from the retained evidence: all 636 historical steps satisfy it; 431 has (delta_V,delta_R,epsilon)=(1,0,0) but eta=1; the ten high-loss controls have (7,6,1). I165's count-decreasing pair has affine dimensions 26 and 28. These are inherited finite report conclusions, not freshly tested facts. A formal rank pattern is not a fully specified graph step. No new graph or counterexample certificate is offered.

## 6. One precise remaining assertion and consequence limits

> **J192, unpaid:** For every admissible target step with N00≠∅ and the actual complete families above, Delta=delta_V+epsilon−delta_R≤1; whenever Delta=1, beta∉L0+U.

For the full I168–I170 class this is the universal assertion; restricting the same assertion to brace steps is the exact brace version, also unpaid. This is equivalent to original exchange because eta is either zero or one. Its complete failure locus is Delta≥2, or Delta=1 with beta∈L0+U. On short gaps only the second alternative remains; on long gaps both are unresolved. J192 is an honest exact obstruction statement, not a theorem obtained by renaming the target.

Thus **EXCHANGE PROVED** and **EXCHANGE REFUTED** are both unsupported; the original-target verdict is **UNRESOLVED**. No Q164 consequence is asserted. Historically Q164 denotes the count bound h(G)≥n/2+2 in I164/I165; the brief focuses on the stronger affine equality d(G)=n/2+1 for braces. The latter implies the former by the minimum size of an affine spanning set. The conditional cube/square/splice dimension arithmetic and prism tightness chain are written in the analytic attempt. They do not close an induction while J192 is unpaid, or assume an unread all-brace generation theorem.

## 7. Source and contribution boundary

Actual manuscript reading is recorded with ranges and theorem labels in [literature.md](../sources/i192_exchange_residual/literature.md); no external theorem was invoked unread. The matching lemma and the coefficient identities are justified in writing. There is no literature priority claim or independent external peer review. The main new deduction at this reading scope is (4), with the exact long-arc component count; it is not nominated as a substantial finding.

Exactly the five brief-assigned files were written. There was no research code, graph/state/matching scan, test, experiment, sealed-computation rebuild or replay, source copy, snapshot, seal, further agent, ancestor/shared-ledger edit, staging, commit, archive or publication. Report hashes bind inherited evidence only. The initial truncated catalogue/report reads and the unsuccessful written approaches remain documented. Final output hashes are returned detached, so no self-hash or seal is introduced.
