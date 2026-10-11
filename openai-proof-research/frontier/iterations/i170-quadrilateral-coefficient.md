# I170 — quadrilateral coefficients and exact boundary residuals

Date: 2026-10-10. Research iteration, not a novelty or acceptance nomination.

**Outcome.** I169's F169, S169, P169, and the 206-step coefficient data pass independent audit in their original scope. The quadrilateral equality-case exclusion remains open. New theorem H170 proves `t >= ell-1` whenever either cross-terminal pair is an edge, and therefore for **every admissible facial hexagon expansion** as well as quadrilaterals. New theorem R170 gives exact class-by-class boundary-residual generators, including the old directions that a longer boundary fails to recover. The tempting assertion `V subset U`, even `V subset L+U`, is false: a certified octagonal example has one old direction missing. It still satisfies exchange. Neither requested target inequality is refuted.

Every theorem in the OpenAI repository at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated true. No upstream theorem was audited, and no contradiction or ex-falso argument was used. The actual `cor:pfaffian-paths` statement, including its stated applicability to planar graphs, was read in `frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`, lines 812–828. This stipulated P4 result is the only upstream existence theorem used below. Family 180 in the pinned catalogue lists this manuscript; no additional companion statement is used.

Only the three authorized I170 locations were written. No ancestor source was executed, imported, or used as implementation; reports and JSON supplied statements and data. No agents, commits, staging, publishing, or shared-ledger edits were used.

## 1. Authentication and audit before the attack

The initial checks, retained in `frontier/sources/i170_quadrilateral_coefficient/initial-hash-check.json`, match exactly:

- I169 report: `1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf`.
- I169 seal: `536a161d0d0f0bf481572d25b4e98920e10b1e705e1afaa9b8dab407f0f8ba7c`.

The seal's inventory and prevalidation bindings and every inventory entry were also authenticated by hashing bytes; ancestor Python was not run. I169's non-context external bindings match. The inherited context drift was recorded separately. The I170 external bindings include all four shared context ledgers; replay-policy.json explicitly excludes only their mathematical enforcement, and the verifier emits drift receipts.

The fresh owned toolkit uses vertex-path DFS for cycles and spanning paths, independently checked against a vertex-by-vertex degree-assignment enumerator with connected-component filtering. Paired two-path covers are enumerated by prescribed degrees and their endpoint components. For every census child, complete cycle sets from both enumerators equal the six lifted fibres. All parent and child graphs are checked for simplicity, cubic degree, bipartiteness, two-vertex-deletion connectivity, oriented face incidence, vertex-link cycles, and Euler characteristic two.

Every rank used in a reported diagnostic is cross-checked by two separately written exact implementations: primitive integer row elimination and Fraction elimination on the transpose. This is not a modular-rank heuristic. All graph, path, cycle, and rank diagnostics use only standard-library Python and no network.

The first cases of the audit and each attack diagnostic are index 0 followed by `520,522,524,527,528,530,533,534,536,539`, read as data from the authenticated ancestor chain and recomputed. They give `(ell,t,eta)=(1,0,1)` and ten copies of `(7,6,1)`, respectively. No candidate bypasses these tests.

### 1.1 Notation

Let B be the finite simple cubic bipartite planar 3-vertex-connected graphs, with a specified plane embedding. An admissible C4 expansion deletes disjoint cofacial edges `e=uv`, `f=xy`, whose terminals occur in cyclic order `u,v,...,y,x,...`, and introduces arms `up,vq,xr,ys` and square `pq,qs,sr,rp`, producing another graph H in B. Put `K=G-{e,f}`. All spaces are over Q, with old edge coordinates extended by zeros where necessary. `diff(F)` is the span of pairwise incidence-vector differences in F, and is zero for an empty or singleton family.

`Nij` consists of parent Hamiltonian cycles with e-status i and f-status j. The surviving family is `S=N10 union N01 union N11`, and `L=diff(S)`. The three new exterior classes are spanning ux paths `Pux`, spanning vy paths `Pvy`, and spanning two-path covers `D11` paired u-v and x-y. Set

    L0 = diff(N10)+diff(N01)+diff(N11),
    U  = diff(Pux)+diff(Pvy)+diff(D11),
    V  = diff(N00),
    ell = d(G)-dim L,
    t   = dim(L+U)-dim L.

Choose `C0 in S`, `P in Pux`, `Q in Pvy`, and `D in D11`. Then

    b = P+Q+D+2e+2f-3C0,
    eta = dim(L+U+<b>)-dim(L+U).

An edge in a vector expression means its unit incidence vector. Cross-class offsets are retained throughout; none of CW167's incorrect aggregated equations is reinstated.

### 1.2 F169 — PASS ORIGINAL

The six P4 applications in H are independently reconstructed. The paths `p-r-s-q`, `r-p-q-s`, `p-q-s-r`, and `q-p-r-s` force, respectively, N10, N01, Pux, and Pvy: their two end vertices must use their arms, since closing the new square cannot be a spanning cycle. The path `u-p-r-x` saturates p,r, excludes pq,rs, and forces `v-q-s-y`, giving D11. The path `u-p-q-v` excludes pr,qs and forces `x-r-s-y`, giving N11. The stipulated P4 corollary therefore supplies all six fibres. Complete finite enumeration checks these forcing statements for every child cycle containing each specified path, as well as existence, on all 636 steps.

Restriction `rho` to e,f gives the three surviving affine signatures `(1,0),(0,1),(1,1)`. They are affinely independent. If a surviving affine difference has zero rho, its coefficient totals in all three classes vanish separately. Hence

    rho(L)=Q^2,   L intersect ker rho=L0,
    dim L=2+dim L0,
    dim(L+U)=2+dim(L0+U).

For `A in N10`, `B in N01`, `C in N11`, define

    beta=P+Q+D+2e+2f-A-B-C.

Its deleted coordinates are zero. At each terminal P+Q+D has degree four, and at each other old vertex degree six; adding 2e+2f gives degree six everywhere. Subtracting A+B+C therefore gives zero vertex degrees. Thus `beta in ker A_K`. Moreover `b-beta=A+B+C-3C0 in L`. Since beta has zero deleted coordinates,

    eta = dim(L0+U+<beta>)-dim(L0+U).

If `N in N00`, the fourth affine signature `(0,0)` introduces exactly the affine relation `N-A-B+C`. Thus

    c=N-A-B+C in ker A_K,
    d(G)=2+dim(L0+V+<c>).

For completeness, the independent child-rank argument uses the two homogeneous coordinates `(arm_up-arm_vq, square_pq-arm_xr)`. Transported differences have image zero; the three new-class reference differences have images `(1,0),(-1,1),(0,-1)`. Their only relation is their sum. Within-fibre differences pull back to L+U, and that sum pulls back to b. The kernel on degree differences is exactly the transport image: writing the four arm values as U,V,X,Y, zero image forces `U=V`, `X=Y`, `pq=X`, `rs=U`, `pr=qs=-U-X`. Reading K and U,X recovers the old homogeneous degree vector. Consequently

    d(H)=2+dim(L+U+<b>).

Combining these identities proves precisely

    exchange iff dim(L0+U+<beta>) >= dim(L0+V+<c>).

If N00 is empty then ell=0 and exchange follows directly. Every numerical rank identity, degree identity, rho rank, beta/b equivalence and offset identity above was independently tested on all 636 steps. The proof is universal; that test range is not its justification. In particular deleted-edge coordinates alone cannot distinguish b from L+U, because rho(L) is already all of Q^2.

### 1.3 S169 — PASS ORIGINAL

For face `u-v-y-x-u`, put `a=ux` and `c'=vy`. A cycle in N00 uses both remaining incident edges at every terminal, so uses a,c'. Deleting a gives a spanning ux path. Conversely a spanning ux path in K cannot contain ux: both endpoints would have their sole path edge in common, isolating a two-vertex component, whereas G has more than two vertices. Adding a closes one spanning cycle avoiding e,f. This proves the first bijection in both directions. The vy version is identical.

Deleting a,c' from an N00 cycle gives two paths. In the closed disk complementary to the open quadrilateral, the alternating-endpoint pairing u-y/v-x is impossible by separation of the disk by a simple arc. Pairing u-x/v-y would close **two** cycles when a,c' were restored, contrary to the original Hamiltonian cycle. Thus the pairing is u-v/x-y. Conversely a D11 cover cannot contain a or c': such an edge would connect a prohibited endpoint pair into its own completed path. Adding a,c' joins its two components to one cycle. This proves the third bijection in both directions.

All three maps are translations of incidence vectors. Therefore `U=V`, and P4 nonemptiness implies N00 nonempty. For `r=N-C0`, `s=e+f-a-c'`, and `W=L+V`, the parent difference space is `W+<r>`. Hence `ell-1 <= t <= ell`. Taking the three new representatives from one N gives exactly `b=3r+2s`; arbitrary choices change it only by W.

In the equality case `t=ell-1`, r is nonzero modulo W. If s is outside the parent difference space then the bridge is independent. Otherwise the unique rational alpha with `s=alpha*r mod W` satisfies

    exchange iff 3+2alpha != 0 iff alpha != -3/2.

These are equivalences, not an exclusion theorem. Exact edge-set equality verifies all six directions of the three bijections on the 206 quadrilateral steps, and both rank implementations verify the quotient calculation.

### 1.4 P169 — PASS ORIGINAL

An independent exhaustion for `C_L square K2`, L even and L>=4, is useful. If a Hamiltonian cycle selects some but not all rungs, each block of consecutive selected rungs has even length. The omitted horizontal edges in each layer form the unique perfect matching of that block. The omissions therefore coincide in both layers. Two or more omitted edges per layer give multiple cycle components; connectivity forces exactly one omitted edge in each layer, at the same position j. These are the L cycles C_j. If all rungs are selected, each layer's selected horizontal edges form one of the two alternating perfect matchings of the even cycle. Equal choices give disjoint squares; unequal choices give exactly the two Hamiltonian cycles X,Y. Zero selected rungs gives two layer cycles. This proves the complete list without relying on ancestor code or a new upstream premise.

In an affine dependence among these L+2 vectors, top-minus-bottom horizontal coordinates force the coefficients of X,Y to agree, say x. Writing S for the sum of coefficients of the ordinary cycles, each horizontal coordinate gives `a_j=S+x`, while the coefficient sum gives `S=-2x`. Thus `a_j=-x` and `(L-2)x=0`. They are affinely independent, so d(G)=L+1.

With rails t_i,b_i and rungs r_i, direct coordinate comparison gives

    (L-2)(r_0+r_1-t_0-b_0)
       = (L-3)C_0 - sum_{j != 0} C_j + X+Y.

The coefficients sum to zero. At a horizontal edge the right side is `-(L-2)` at index 0 and zero elsewhere. At rung i, only C_i and C_(i-1) contribute among the ordinary cycles; X,Y each contribute one. The result is L-2 exactly at i=0,1, and zero otherwise. This proves the integral identity at every coordinate and for every even L>=4.

Deleting r_0,r_1 leaves exactly five surviving cycles `C_(L-1),C_0,C_1,X,Y`; N00 contains the other L-3 ordinary cycles. Affine independence gives `(ell,t)=(L-3,L-4)`. Summing their coefficients in the identity gives `alpha=-(L-3)/(L-2)`. For deleting t_0,b_0, N00 is just C_0, all other cycles survive, and s is the negative of the displayed square vector. This gives `(ell,t)=(1,0)` and the same alpha. Thus `3+2alpha=L/(L-2)>0`, eta=1, and d(H)=L+3 for both deletion types. Rotations and layer exchange cover every lateral face.

Admissibility does not hide a connectivity assumption. The prism is simple, cubic and bipartite; two deleted vertices leave connected layer paths joined by rungs, or one intact layer connecting the other remnants. Its usual embedding is planar. Expansion gives four distinct new vertices, alternating arms and an embedded square, so simplicity, cubic degree, bipartiteness and planarity persist. For 3-connectivity of a child: two deleted old vertices leave the parent connected, and the intact square supplies replacement routes and attaches to the remaining terminals. Two deleted new vertices leave old vertices connected in G-{e,f}, because a 3-vertex-connected cubic graph has no edge cut of size at most two; each surviving new vertex has an old arm. With one old and one new deletion, the remaining square is a connected three-vertex path. If the old vertex is a terminal, the parent minus that vertex is 2-connected and remains connected after the other deleted edge is removed. Otherwise every component obtained by removing e,f from that 2-connected graph must meet at least two terminals: one terminal would yield a bridge, and no terminal would already be disconnected. The square path attaches to three of the four terminals and joins all components. This also handles fewer deletions.

The fresh numerical validation covers every even L from 4 through 18 and both deletion types, with complete enumerator agreement, coordinate equality, exact ranks and all admissibility checks. The analytic argument supplies the infinite quantifiers.

### 1.5 Original data — PASS ORIGINAL

All 636 steps on the 15 specified parents reproduce

    (ell,t,eta)=(0,0,0):138; (1,0,1):385; (1,1,0):56;
                (3,2,1):34; (5,4,1):13; (7,6,1):10.

The 206 quadrilateral steps reproduce

    (0,0,0):12; (1,0,1):127; (1,1,0):12;
    (3,2,1):32; (5,4,1):13; (7,6,1):10.

Among their 182 equality cases, alpha is exactly `-1/2` (72), `-3/4` (20), `-5/6` (28), or `-7/8` (62). There is no original failure to narrow or repair in the four assigned I169 items. This does not independently audit every earlier claim mentioned as I169 context.

## 2. Obligation (i): quadrilateral equality case — still open

The attack tested the suggested candidate `alpha=-(m-1)/m` with a positive integer m, equivalently `m=1/(1+alpha)`. The mandatory cases were evaluated first. The additional, completely enumerated bounded scan takes every quadrilateral and both deletion pairs in all 52 graphs of order at most 28 in I166's bound `walks` JSON dictionary. These are input graphs, not an exhaustive isomorphism census. The fresh enumerators, degree/surface/connectivity checks and two exact ranks were used; no ancestor cycle list was taken on trust.

There are 914 additional steps, of which 610 have a nonzero equality quotient. Their alpha histogram is

    -3/4:12; -5/6:28; -7/8:62; -9/10:196; -11/12:312.

Every recorded m is a positive integer. In this particular additional sample each equality coefficient also equals `-(n/2-3)/(n/2-2)`. The original census has non-brace examples governed by smaller pieces, so that order-only expression is not a general statement about B. Neither the integer shape nor `-1<alpha<0` has been proved universally. No alpha=-3/2 example or example with s outside the parent difference space occurred in this bounded scan.

The geometric reformulation is exact but does not solve the gap. For N in N00, switching the square produces `F=N+s`, a spanning 2-factor with two components, since its exterior is paired u-v/x-y. Normalize a linear functional annihilating W by `w(r)=1`. When s is in the parent span, `w(F-C0)=1+alpha`. The forbidden alpha=-3/2 is equivalent to this value being -1/2. A proof that this particular disconnected 2-factor cannot have that normalized value would finish the equality case. Hamiltonian-cycle weights alone do not provide that bound; treating F as a convex combination of Hamiltonian cycles would be an additional unproved assumption. No positivity, integrality, bounded dual-transfer, or typed-fullness premise is smuggled into the argument.

## 3. Obligation (ii): a universal short-gap theorem

**Theorem H170.** For every admissible expansion as in Section 1, if `a=ux` is an edge of K, then N00 is nonempty and there are exact translation bijections

    N00 -> Pux,  N |-> N-a,
    Pvy -> D11,  Q |-> Q-a.

Consequently, with `Z=diff(Pvy)`,

    U=V+Z,  and t>=ell-1.

The same assertions hold with the pairs ux and vy interchanged. In particular the inequality holds for every admissible expansion of a face of length four **or six**. A counterexample to `t>=ell-1` must therefore have face length at least eight, with neither cross-terminal pair an edge.

**Proof.** K has degree two at each of the four terminals. Every N00 cycle therefore uses a, and removing a gives a spanning ux path. The reverse map is valid because a spanning ux path cannot contain its endpoint edge a; adding it closes a single spanning cycle in K. P4 supplies a Pux path, hence an N00 cycle. This first bijection does not require that vy be an edge.

A spanning vy path Q uses a because u,x have degree two in K and are not its endpoints. Removing a breaks Q into two paths. Its u,x endpoints lie in different components; the remaining possible pairing other than u-v/x-y is the crossing pairing u-y/v-x, excluded by the plane disk argument. Conversely a D11 cover avoids a and adding a joins its two paths to one spanning vy path. Thus the second bijection is exact. Subtracting fixed vectors preserves differences, giving U=V+Z. The parent difference space is `L+V+<r>`, where `r=N-C0`, so its dimension is at most `dim(L+U)+1`. This is precisely `t>=ell-1`.

On a bipartite face an admissible pair of deleted edges has odd-length complementary arcs u-to-x and v-to-y: u,x have opposite colors, as do v,y, from bipartiteness of the child square and arms. For face length six those two positive odd lengths sum to four, so one is one. For length four both are one. This proves the face-length consequences. No assertion about bounded bidirectional transfers or typed affine fullness is used.

The bridge offset also stays exact. Assume a exists, choose `N in N00`, `Q in Pvy`, and let

    r=N-C0,
    z=Q+e+f-a-C0,
    W'=L+V+Z=L+U.

Taking `P=N-a` and `D=Q-a` gives `b=r+2z`; other choices give the same equation modulo W'. Both r,z have zero degrees. If `t=ell-1`, then r is nonzero modulo W' by dimension, and exchange fails exactly when `z=-r/2 mod W'`. This is a useful short-gap analogue of S169, not a proof of hexagonal exchange. F169's beta,c remain the authoritative deleted-edge-free offsets.

Fresh finite checks verify both bijections, their inverses, the space identities and this bridge equation on all 580 short-gap steps in the original census, starting with the mandatory cases. They include all 282 hexagonal steps. The two hexagonal high-loss cases, indices 177 and 180, have `(ell,t,eta)=(3,2,1)` and are covered by the theorem.

## 4. Exact correction on arbitrary longer faces

A blanket formula `diff(Pux)=V+extra`, or even `U=V+extra`, is generally false. The exact replacement must record which old N00 directions survive the boundary operation.

**Theorem R170.** Suppose N00 is nonempty. Let A be the boundary arc from u to x avoiding e,f, and B the boundary arc from v to y. Both have odd length. For an odd arc with edges h_0,...,h_(2k), put

    q_A=h_0-h_1+h_2-...+h_(2k),

and define q_B similarly. For J equal to Pux, Pvy, D11 use, respectively, `q_J=q_A,q_B,q_A+q_B`. Define the explicit compatible old subfamily

    F_J={N in N00 : N-q_J is a 0/1 incidence vector
                       and has the connectivity and endpoint pairing of J}.

Equivalently, N uses every positively signed boundary edge, avoids every negatively signed one, and the toggled graph is the required spanning path or paired cover. This is a finite graph-theoretic condition, not a rank assumption. Define the residual class

    R_J={P in J : P+q_J is not in N00}.

If F_J is nonempty choose N_J in F_J, put `P_J=N_J-q_J`, and form

    E_J={P-P_J : P in R_J}.

Then the exact individual correction is

    diff(J)=diff(F_J)+span(E_J),       diff(F_J) subset V.        (R170.1)

If F_J is empty, choose any P_J in J and set `E_J={P-P_J:P in J}`; use `diff(F_J)=0`. Formula (R170.1) still holds. The six-fibre theorem ensures J is nonempty.

**Proof.** At each internal arc vertex the two signed incident boundary coefficients cancel; at each endpoint the degree of q is one. Thus subtraction has exactly the required degree defect, whenever its entries are 0/1. The stated connectivity/pairing test is exactly what additionally makes it a member of J. The translation N -> N-q_J is injective and has image `J\R_J`; its inverse is addition of q_J. Pairwise differences within that image are precisely diff(F_J). Taking differences from one image anchor adds exactly the displayed residual vectors. If the image is empty, all members are residual and the ordinary reference-vector formula for a difference span applies. This proves (R170.1) in both directions, including all class offsets.

Set

    V_good=sum_J diff(F_J),   R=span(union_J E_J).

Then `V_good subset V`, `U=V_good+R`, exactly. In F169's K-space set

    delta_V=dim(L0+V)-dim(L0+V_good),
    delta_R=dim(L0+V_good+R)-dim(L0+V_good),
    epsilon=dim(L0+V+<c>)-dim(L0+V),  epsilon in {0,1}.

Rank subtraction gives the exact deficit identity

    ell-t = delta_V+epsilon-delta_R.                        (R170.2)

Consequently the general lower-bound problem is precisely

    t>=ell-1 iff delta_R >= delta_V+epsilon-1.               (R170.3)

Full exchange retains beta and is precisely

    delta_R+eta >= delta_V+epsilon,
    eta=dim(L0+V_good+R+<beta>)-dim(L0+V_good+R).             (R170.4)

If N00 is empty, ell=0 and the lower bound and exchange are immediate; no N00 anchor is introduced. For quadrilaterals every F_J is N00, there are no residuals, and these formulas reduce to S169. For a short gap the associated one-edge arc has F_J=N00, so `V_good=V` and (R170.3) is automatic. For two genuinely longer arcs, the missing old generators and the residual gains must both be accounted for. This is the precise remaining obstruction; simply adding generators to all of V is not an exact correction.

Every equality above is checked by both exact ranks on all 636 original steps; the payload retains each q_J, anchor, residual generator, and deficit. At index 14 (a hexagonal step), the Pux and D11 translated images are empty although each full class has three members, whereas Pvy has the one old-cycle image. This explicitly refutes extending all three quadrilateral bijections without residuals.

### 4.1 Certified failure of the blanket containment shortcut

The fresh enumeration gives `U not containing V` at indices 263,272,431, all octagonal expansions on 20-vertex parents. Each has `rank U=8` and `rank(U+V)=9`. The retained certificates list complete graphs, embeddings, labels, class edge sets, a rationally independent old difference, and an integer weight annihilating every within-new-class difference but not that old difference. These are exact counterexamples to containment, not to either requested exchange target. No global minimality of their graph order is claimed.

Index 431 is especially relevant: `(ell,t,eta)=(1,0,1)`, and `(delta_V,delta_R,epsilon)=(1,0,0)`. Thus even `V subset L+U` fails. Its sorted old edges are

    02,04,08,13,15,(1,19),26,(2,10),37,(3,11),46,(4,16),57,(5,15),
    (6,12),(7,13),89,(8,10),(9,11),(9,18),(10,11),(12,13),(12,14),
    (13,15),(14,15),(14,17),(16,17),(16,18),(17,19),(18,19).

Here two-digit strings mean pairs of single-digit vertices. The step is `[0,0,4]`, with `(u,v,x,y)=(2,10,13,7)`. In that edge order the separator and old difference are

    w=(1,1,0,-2,2,0,0,0,-3,0,-1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,-1,0,0,0),
    v=(0,-1,1,1,-1,0,0,0,0,-1,1,0,0,1,-1,0,-1,0,1,0,0,0,1,0,-1,0,1,-1,-1,1).

Direct dot products give `w.U=0` and `w.v=-8`. The rank-based failure modulo L is separately verified by (R170.2); the displayed w is only asserted to annihilate U. No claim is made that this particular w annihilates L. Complete unambiguous integer-pair edge data are in `refuted-proposals.json` and the residual payload.

## 5. Longer-face search and remaining scope

The original data have 430 longer-face steps: 282 hexagonal, 108 octagonal, and 40 decagonal. No step has `t<=ell-2`. The deficit correction histogram records just three cases with `delta_V=1`: two recover it by `delta_R=1`, while index 431 has epsilon=0 and loses exactly one direction. A separate complete bounded scan takes every admissible longer-face edge pair in all 23 I166 `walks` graphs of order at most 24. It covers 982 steps, with face lengths 6,8,10,12, and no target counterexample. Its survival losses are only zero or one, so it is weak evidence about the difficult high-loss longer-face regime. It is not a census of all graphs through order 24.

The minimum *possible face length* of a lower-bound counterexample is now proved to be at least eight by H170. No graph with `t<=ell-2`, at that length or otherwise, has been found or certified. The exact remaining general lower-bound gap is (R170.3) when both boundary arcs have length at least three. The general bridge gap is (R170.4), even after the lower bound is supplied. For hexagons the lower bound is settled here, but bridge independence in its equality case remains open.

## 6. Evidence, replay, sources and limits

The owned directory is `frontier/experiments/i170_quadrilateral_coefficient/`; receipts are in `frontier/sources/i170_quadrilateral_coefficient/`. The authoritative modules are `core.py`, `audit.py`, `prism.py`, `coefficient.py`, `residual.py`, and `longscan.py`. The final residual payload is attempt 03. Attempts 01 and 02, their source snapshots, outputs, and stderr files remain. Attempt 03 adds the short-gap bridge check and reproduces attempt 02's payload bytes. All declared bounded scans completed; there was no diagnostic crash, timeout, or truncated declared scan. Refuted proposals are retained rather than removed. Early development runs are explicitly development runs; the immutable-first contract applies to the final prevalidation and sealed diagnostic replay, which start only after the final report and all diagnostic inputs/outputs are bound.

`verify.py` authenticates the final report, all owned non-control bytes, and all non-context external bytes before loading or executing a diagnostic. The inventory and successful prevalidation are control files bound by `seal.json`; the final externally reported seal hash closes that chain. The seal is created with exclusive-create exactly once, after successful `--prevalidate`, and is never resealed. The final verifier invocation is read-only. Hashes and runtime are returned outside the report so its bytes need no post-seal changes.

A read-only Python audit hook rejects writes, filesystem mutations, network, subprocesses, unbound repository reads, and compile/exec outside bound owned sources or the trusted Python standard library. It rejects owned-source compilation whose bytes differ from the pre-bound source. Guard probes explicitly exercise writes, mutations, network, subprocess, outside compile, outside exec, unbound reads, and forged owned source. Trusted standard-library code and runtime binaries are runtime dependencies, not unbound repository mathematics. Every successful diagnostic version is replayed and compared byte-for-byte to its deterministic JSON payload. Retained non-executed snapshots and refutation receipts are also byte-bound.

`README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` are bound as context in external-bindings.json and explicitly listed as context-only exclusions in replay-policy.json. Initial and preparation drift receipts are retained; subsequent replay drift is emitted read-only. No graph, ancestor diagnostic, theorem statement, report, or owned mathematical input receives this exemption.

The literature-search receipt records the actual queries and successful primary-page inspections: [Gorsky–Steiner–Wiederrecht](https://arxiv.org/abs/2202.11641) and [Florek, Remarks on Barnette's conjecture](https://link.springer.com/article/10.1007/s10878-019-00460-8). The first inspected abstract concerns brace reductions and strengthened Hamiltonicity. The second gives cycle-count and face-prescription results under a facial quadrilateral 2-factor hypothesis. Neither inspected statement is the affine coefficient exclusion studied here. No theorem from those searches is used. No retrieval was blocked; not finding a matching statement is not a novelty certificate. The results here are only new-to-this-iteration deductions, with literature priority unestablished.

No finite result establishes affine fullness, the brace target (T), Q164, or universal exchange. D168's bounded-bidirectional-transfer obstruction and M168's typed-fullness counterexample are respected, and the deleted-coordinate separator route remains excluded by the independently verified rho(L)=Q^2 calculation.

## 7. Exact claim status and recommended next action

**Proved:** the four assigned I169 audit items pass in their original mathematical scopes. H170 gives exact short-gap bijections, `U=V+Z`, the bridge relation `b=r+2z mod (L+U)`, and `t>=ell-1` for every short-gap expansion, hence every facial hexagon expansion. R170 gives exact residual generators for all three classes and the universal deficit/exchange comparisons (R170.2)–(R170.4). Blanket containment `V subset U`, and even `V subset L+U`, is refuted by certified octagonal examples; these are not counterexamples to exchange.

**Finite evidence:** all 636 original steps and the original 206-step coefficient histogram are independently reproduced; both deletion types are validated on even prisms through L=18; 914 additional quadrilateral steps through parent order 28 and 982 additional longer-face steps through parent order 24 show no target failure. The integer coefficient shape remains an observation.

**Open:** exclusion of alpha=-3/2 for every quadrilateral equality case; universal exchange even on hexagons; (R170.3) for longer faces with no short gap; the general exchange step, (T), and Q164. No target counterexample or universal quadrilateral-exchange proof is claimed.

**Recommended next action:** first seek a proved constraint on the normalized weight of the disconnected square-switch 2-factor, equivalent to excluding the single value -1/2. Separately focus the lower-bound search and proof on octagonal faces whose two complementary arcs both have length three, using R170's missing-old and residual-gain spaces. Index 431 must be added to the existing mandatory tests for any proposed old-direction containment argument. Keep beta and c exact; neither a positive relation nor full recovery of V may be assumed.
