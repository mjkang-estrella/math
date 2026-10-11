# I189 analytic attempt: symbolic patch routes and survivor transport

2026-10-11. **COMPLETE WRITTEN ATTEMPT — ORIGINAL E183: UNRESOLVED.** Ten degree-feasible patterns, seven cycle-free candidates, exact admissibility and conditional transports are proved below; Section 5 identifies every open class. Unsealed proof-only record, written incrementally. At checkpoint 1 only authentication, required reading, exact hypotheses and Sections 1–2 were complete; later sections were then still pending.

## 0. Exact unchanged hypotheses and original quantifier

For every finite connected simple bipartite locally cubic disk X, its five distinct degree-two ports b_0,...,b_4 have boundary order (0,2,1,4,3), and colors (1,1,1,0,1) in LABEL order. Every other vertex is cubic. Join b_i by e_i to, respectively, (1,5,6,28,29) of a disjoint exterior Y. The vertex set of Y is {1,...,11,28,29}, and its internal edges are exactly

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

The resulting G is simple, planar, bipartite and a brace. Here the brace hypothesis retains its original meaning; in this setting its two-edge matching extension consequence and the I187-reviewed small-cut deductions are available. A local packing spans its side, has degree one precisely at the used ports and degree two elsewhere, and has no cycle component. A fibre consists of ALL such packings of its specified used set and endpoint pairing, not selected representatives. Compatible exterior products are complete. The eleven complete nonempty survivor fibres are

```
02;02   12;12   14;14   24;24
0123;02,13   0123;03,12   0134;03,14
0234;02,34   0234;03,24   1234;12,34   1234;14,23.
```

The complete lost fibres are P=(01;01) and D=(0134;01,34). The internal port-disjoint simple six-cycle C=(x,a,b,y,d,c,x) has chord xy. Put A={xa,by,dc} and B={ab,yd,cx}. For every admissible choice of p in P with E(p) intersect E(C)=A and q=p symmetric-difference E(C) also in P, the target is SOME perfect matching M of G containing A for which G-M is a Hamiltonian cycle of ANY survivor local type. Both p and q are local packings here; they are not the sought perfect matching. No specified completion, cut-2 prescription, single symmetric-difference cycle, or sequence of moves is part of the quantifier.

The four remaining patch incidences are aa',bb',cc',dd', with four distinct terminals outside C; each belongs to X, possibly to its port set. Color x,b,d black and a,y,c white, so a',c' are black and b',d' white. These patch colors need not agree in name with the numeric port colors. Write V_C={x,a,b,y,d,c}, R=G-V_C, and E_patch=E(C) union {xy,aa',bb',cc',dd'} (eleven edges). All patch vertex degrees in G are three. The two squares are facial, their interiors form an empty patch disk, and its outgoing incidences have cyclic order (a,b,d,c), by the paid I188 geometry. The complement of a small closed neighborhood of this disk is a disk containing R and the truncated outgoing incidences.

All ten I187/I188 anchors and the manuscript anchor matched before new proof work. I188 and both finalized dispositions are read inputs, not research controls to rerun. The paid exterior criterion is

    H survives iff 2 belongs to U(H), or theta(H)=14;14,
                    or theta(H)=0134;03,14.                    (S)

The nine cut-2 types plus the two stated no-cut-2 types are exactly the eleven above. This is used for full local type, not only cut membership.

## 1. Complete symbolic classification of the eleven-edge restriction

Use T for the subset of continuation LETTERS used by a degree-two restriction; thus T=ab means aa',bb' are used, not edge ab. Every omitted continuation is absent. Each table entry lists every internal path or cycle; adding the endpoint continuations shown gives the full restriction. Reversing a displayed path changes nothing. Define terminal pairings

    alpha=(a'b')(c'd'), beta=(a'c')(b'd'), gamma=(a'd')(b'c').

| Name | xy used? | T | Complete internal restriction | Terminal pairing / defect |
| --- | --- | --- | --- | --- |
| Z | no | empty | cycle x-a-b-y-d-c-x | isolated six-cycle |
| L_ab | no | ab | a-x-c-d-y-b | a'b' |
| L_cd | no | cd | c-x-a-b-y-d | c'd' |
| F | no | abcd | a-x-c and b-y-d | beta |
| K_B | yes | abcd | a-x-y-b and c-d | alpha; complementary matching uses B |
| Z_top | yes | cd | cycle x-a-b-y-x and path c-d | isolated four-cycle |
| K_A | yes | abcd | a-b and c-x-y-d | alpha; complementary matching uses A |
| Z_bottom | yes | ab | cycle x-y-d-c-x and path a-b | isolated four-cycle |
| L_bc | yes | bc | b-a-x-y-d-c | b'c' |
| L_ad | yes | ad | a-b-y-x-c-d | a'd' |

The terminal extensions are literal, e.g. L_ad is a'-a-b-y-x-c-d-d', and K_A consists of a'-a-b-b' and c'-c-x-y-d-d'. The seven rows without a cycle are all candidate Hamiltonian restrictions. The three Z rows are degree-feasible restrictions but never restrictions of a Hamiltonian cycle here, because Y is nonempty and disjoint from that closed component.

**Completeness proof.** If xy is absent, degree two forces xa,xc,yb,yd present. The a,b equations say ab+aa'=ab+bb'=1, while the c,d equations say cd+cc'=cd+dd'=1, with variables indicating use. Thus the two choices ab,cd are independent bits. Values (1,1),(0,1),(1,0),(0,0) give Z,L_ab,L_cd,F respectively; nothing else is possible.

If xy is present, x chooses exactly one of xa,xc and y exactly one of yb,yd. For choice (xa,yb), absence of xc,yd forces cd,cc',dd' present. The remaining bit ab gives K_B when absent and Z_top when present. For (xc,yd), absence of xa,yb forces ab,aa',bb' present. The bit cd gives K_A when absent and Z_bottom when present. For (xa,yd), absence of yb,xc forces ab,bb',cd,cc' present, so aa',dd' are absent: precisely L_bc. For (xc,yb) the same equations force ab,aa',cd,dd' present and bb',cc' absent: precisely L_ad. These four choices exhaust degree two at x,y. There are exactly ten degree-feasible restrictions, of which exactly seven have no closed component. This is written Boolean case analysis, not enumeration by code.

The complementary local matching edges are also explicit:

| Restriction | Matching edges incident to V_C |
| --- | --- |
| K_A | xa,by,dc |
| K_B | ab,yd,cx |
| F | xy,ab,cd |
| L_ab | xy,cc',dd',ab |
| L_cd | xy,aa',bb',cd |
| L_bc | xc,yb,aa',dd' |
| L_ad | xa,yd,bb',cc' |

Each list meets every patch vertex once and meets an outside terminal precisely when its continuation is unused. This verifies the required matching compensation locally; any valid degree-two global replacement has its perfect matching as its cubic complement.

## 2. Exact global admissibility and port threading

### 2.1 What the rest must supply

For a restriction with used continuation set T, H_R=H intersect E(R) has degree one at the terminals in T and degree two at all other vertices of R. In particular an unused terminal has degree two in H_R; it cannot be treated as a free endpoint. In an actual Hamiltonian cycle H_R has no cycle component.

For L_ab,L_cd,L_bc,L_ad, H_R must be one spanning path between the two indicated terminals. This condition is sufficient: adjoining the single spanning patch path produces one spanning cycle. For K_A,K_B,F, H_R must be two disjoint paths spanning R, with terminal pairing rho. The union is one spanning cycle exactly when rho differs from the patch pairing. Contracting the four paths reduces this statement to two perfect matchings on four labels: equal matchings make two doubled-edge components, unequal matchings make one four-cycle. This proves necessity and sufficiency, including the prohibition on additional closed components.

The pairing gamma is excluded in R by planarity. To prove this without assuming the terminals are themselves on a face, extend each R path to the corresponding outgoing cut points on the boundary of the patch neighborhood. These points have order a,b,d,c. An a-to-d arc separates the two other boundary points b,c in the complementary disk, so a disjoint b-to-c arc is impossible. Hence rho is alpha or beta. Consequently

    K_A or K_B: admissible exactly when rho=beta and no R cycle;
    F:          admissible exactly when rho=alpha and no R cycle. (1)

This explicitly handles the alpha obstruction to canonical routes: canonical plus rho=alpha closes TWO cycles.

Bipartiteness imposes no further exclusion of these seven local rows. This statement only checks necessary local color constraints, not global realizability in every admissible X. G is balanced since it is cubic bipartite. Removing V_C removes three vertices of each color, so R is balanced. Its degree deficit on a used terminal is one, hence the number of black used terminals equals the number of white ones. The possible size-two sets are exactly ab,ad,bc,cd; ac and bd are forbidden. A spanning R path in the four two-terminal cases must have opposite-color endpoints, as each listed pair does. For alpha both R paths have opposite-color endpoints; for beta one path has two black endpoints and the other two white endpoints, with their one-vertex color surpluses cancelling. All listed patch path parities agree. Thus parity does not reject F or any L row. The brace consequences pay the embedding and distinct-terminal assumptions used above; no theorem excluding an additional surviving row is established here. A locally allowed row is never asserted globally realized merely from this table.

### 2.2 The five-port type requires the actual rest connections

Let W=X-V_C. Restrict H to W and retain, as separate labelled boundary incidences, each used patch continuation and each used cut e_i. Deleting V_C reduces a used-continuation terminal's degree by one; restricting to X also reduces a used-port vertex's degree by one. If both labels occur at the same vertex, keep both and their zero-length connection. No incidence is discarded merely because its vertex coincides with another endpoint label. A degree-two component with no boundary incidence would already be a forbidden closed local cycle.

Trace these W components as intervals between labelled incidences, then join each patch pair according to the table. A closed component produced during this gluing makes the proposed local packing inadmissible. Otherwise the resulting intervals pair exactly the used port labels U; this pairing pi defines theta=(U;pi). Gluing to Y is Hamiltonian precisely when it yields one cycle (for |U|=2 a spanning Y path; for |U|=4 a different Y pairing). This tracing rule is an exact, lossless description of how T and the patch routes influence type; T alone does not determine theta.

In particular K_A and K_B have the same four labelled endpoints and the same alpha pairing, cover exactly the same six vertices, and introduce no closed patch component. Replacing one by the other while keeping W fixed preserves the existence/absence of any closed component and the entire labelled port pairing. Thus it preserves theta, not just U. For F-to-K_A, the pairing changes beta to alpha, and the full tracing must be redone. For any L-to-K_A, two previously unused incidences acquire use and W must change its degrees at those terminals. Holding W fixed is impossible.

## 3. Transport with all four continuations

### 3.1 K_A and K_B: complete transport, preserving the full type

K_A already supplies the desired M. For K_B replace its two routes by K_A, changing precisely the six edges of C. The outside edges and all four continuations remain fixed. By (1) rho=beta before and after, so the cycle remains Hamiltonian. The complement matching changes its patch edges from B to A and remains perfect. Section 2.2 proves the full type unchanged. Criterion (S) therefore proves survival for every one of the eleven types. There is no iteration or improvement sequence here, only one fully verified replacement.

### 3.2 F: the exact two-cycle obstruction and its cut distribution

Here H_R consists of spanning disjoint paths R_ab and R_cd, by (1). Replacing F by K_A with H_R fixed produces exactly

    Z_ab = R_ab + (a'-a-b-b'),
    Z_cd = R_cd + (c'-c-x-y-d-d').                         (2)

These are disjoint cycles covering G. Every patch vertex still has degree two; the complementary matching changes {xy,ab,cd} to A. The obstruction is connectedness, not existence of that matching.

All five cut edges lie outside the patch. Each R path begins and ends in X, so the number of cut edges it uses is even. Write U_ab and U_cd for their disjoint used-label sets. They partition U. For |U|=2 the distribution is necessarily (2,0) or (0,2). For |U|=4 it is (4,0),(0,4), or (2,2). This statement counts the actual labelled incidences, including a terminal that is an original port.

If either set is empty, the corresponding cycle in (2) lies wholly in X. Changing only Y or its selection of edges, while leaving the used cut edges and the proposed local packing fixed, cannot remove this closed X component. An edge of the rest in X must change. This is a proved obstruction to the fixed-X replacement, not a proof that no more general rerouting exists.

If the distribution is (2,2), each cycle in (2) crosses to Y exactly twice. Each contains exactly one of the two Y paths of the original H. Removing Y leaves a cycle-free spanning two-path packing in X, with pairing pi'=sigma, where sigma is the original Y pairing: each of the two newly closed cycles paired one X path with one Y path on the same endpoints. Originally pi differed from sigma. On four cyclically ordered boundary points there are exactly two noncrossing pairings, so pi' is the other local pairing. To reconnect, replace Y by a spanning packing with pairing pi (different from pi'=sigma), keeping the same U and the new canonical packing in X. This yields one Hamiltonian cycle by the four-label contraction proof.

This is an explicit compensating change outside the patch: change the Y packing from sigma to pi, keeping its attachment set. Its complement changes to the corresponding perfect matching; each attachment's membership stays fixed. The X and Y degree requirements ensure degree two globally, and their different pairings ensure connectedness. The next subsection supplies literal Y paths, rather than assuming such a packing exists.

### 3.3 All exterior reroutings needed for the balanced four-cut case

The following are two disjoint spanning paths in the exact Y for each indicated exterior pairing. Commas between paired labels distinguish port labels, not vertex names. Endpoints use the fixed attachment list (1,5,6,28,29). Each row's paths have disjoint vertex sets whose union is {1,...,11,28,29}; their successive edges all occur in Section 0. Internal vertices have degree two and the four stated endpoints degree one, so these are written witnesses, without any enumeration or claim of a complete cut-2 exterior table.

| U | Exterior pairing | Two explicit Y paths |
| --- | --- | --- |
| 0123 | 02,13 | 1-7-6 ; 5-11-10-4-3-9-8-2-29-28 |
| 0123 | 03,12 | 1-7-8-9-10-4-3-2-29-28 ; 5-11-6 |
| 0234 | 02,34 | 1-7-8-2-3-9-10-4-5-11-6 ; 28-29 |
| 0234 | 03,24 | 1-28 ; 6-7-8-9-10-11-5-4-3-2-29 |
| 1234 | 12,34 | 5-11-6 ; 28-1-7-8-9-10-4-3-2-29 |
| 1234 | 14,23 | 5-11-10-4-3-9-8-2-29 ; 6-7-1-28 |
| 0134 | 01,34 | 1-7-6-11-10-9-8-2-3-4-5 ; 28-29 |
| 0134 | 03,14 | 1-28 ; 5-11-6-7-8-9-10-4-3-2-29 |

For completeness of the written verification, in the first two rows the short paths occupy {1,7,6} and {5,11,6}, respectively; their displayed other paths occupy exactly the ten remaining vertices. In the third and seventh rows the separate edge occupies {28,29}, leaving a path through 1,...,11. In the fourth and eighth rows the separate edge occupies {1,28}, leaving a path through {2,...,11,29}. In the fifth row the short path occupies {5,11,6}; in the sixth it occupies {6,7,1,28}; the other displayed paths cover the respective complements. Comparing adjacent pairs with Section 0 verifies every edge. The endpoint list gives exactly the declared pairings. These are direct symbolic witnesses, not graph scans.

For U=0123,0234,1234 both local pairings appear in the eleven survivor list. Thus every F survivor of these used sets with distribution (2,2) transports to a canonical survivor, by choosing the row whose exterior pairing is the old local pairing. Criterion (S) proves survival because cut 2 is still used. Explicitly the local types interchange as follows:

    0123;02,13 <-> 0123;03,12,
    0234;02,34 <-> 0234;03,24,
    1234;12,34 <-> 1234;14,23.                            (3)

This is survival preservation, not full-type preservation.

For U=0134 a starting survivor has local pi=03,14 and exterior sigma=01,34, by the paid I188 COMPLETE exterior table. Balanced splitting changes the local pairing to pi'=01,34. The eighth displayed row (or either of the other two I188 packings of exterior pairing 03,14) reconnects it, but the resulting local type is D, LOST. Criterion (S) proves it does not survive. This operation therefore fails the target in this case even though it produces a canonical Hamiltonian cycle. Holding the newly obtained X packing fixed, no choice of exterior can change its local type. Keeping the original exterior instead gives the two cycles in (2).

For |U|=2 a survivor has type 02;02,12;12,14;14, or 24;24. Its distribution is unbalanced, so Section 3.2's closed-X obstruction applies to all four types. There is no four-cut reconnection shortcut in these cases.

### 3.4 The exact no-cut-2 exterior input used above

This table is reused from authenticated I188 analytic Section 6.2, whose proof and finalized parent review were read. It is not re-enumerated here. Put

    R1=1-28-29-2-3-4-10-9-8-7-6-11-5,
    R2=1-28-29-2-3-9-8-7-6-11-10-4-5,
    R3=1-28-29-2-8-7-6-11-10-9-3-4-5,
    S =29-28-1-7-6-11-10-9-8-2-3-4-5,
    T_Y=1-7-6-11-10-9-8-2-3-4-5.

| Local X type | COMPLETE compatible Y fibre |
| --- | --- |
| P=01;01 (lost) | R1,R2,R3 |
| 14;14 (survivor) | S |
| D=0134;01,34 (lost) | edge 1-28 plus each Ri with its initial 1,28 removed |
| 0134;03,14 (survivor) | edge 28-29 plus T_Y |

The color balance allows no-cut-2 used sets 01,04,14,0134 only; 04 has no admissible Y packing. For 0134 the only disk pairings are 01,34 and 03,14. This is why changing the exterior alone cannot rescue the lost local pairing in Section 3.3, and why neither cut-2-only reasoning nor an unlabelled patch picture proves survival.

**Historical checkpoint 2:** Sections 0–3 were written before the two-continuation analysis and final verdict. Sections 4–7 below complete the present record.

## 4. Two-continuation cases: degree repair, conditional transports, and exact gaps

### 4.1 Fixed-rest replacement is impossible in all four rows

Let I be the used pair and J its two-letter complement in {a,b,c,d}. In a two-continuation H, H_R is a spanning path with endpoints I'. The J' vertices are interior vertices of that path, each already of degree two. Canonical routes use all four continuations, so adjoining them while holding H_R fixed gives degree three at both J' vertices. There must be a compensating change of the rest edges. The missing pairs are

| Original row | I | J (terminals requiring degree repair) | Matching edges freed when canonical routes are installed |
| --- | --- | --- | --- |
| L_ab | ab | cd | cc',dd' |
| L_cd | cd | ab | aa',bb' |
| L_bc | bc | ad | aa',dd' |
| L_ad | ad | bc | bb',cc' |

Replacing the internal matching edges by A also changes the other patch edges exactly as listed in Section 1. Nothing in this step changes the quantifier to requiring a particular repair.

### 4.2 Existence of a matching repair is paid; its topology and type are not

Put N_H=(G-H) intersect E(R). It is a matching covering every vertex of R except the two J' terminals. This follows vertex by vertex: for I' the continuation is in H, so the matching uses a rest edge; for J' the matching used the omitted continuation; all nonterminals remain matched inside R. The known packing q, completed by any of R1,R2,R3, gives a canonical Hamiltonian cycle: q uses exactly B on C, so the degree equations put it in K_A. Its complementary matching contains A, and deleting A supplies a perfect matching N_q of R. This is also the paid I183 matching-deletion bijection.

In N_H symmetric-difference N_q, every vertex other than J' has degree zero or two and each J' vertex has degree one. Edges alternate between the two matchings. Finiteness therefore gives exactly one path L between J' and possibly disjoint even cycles. L starts and ends in N_q, has odd length, and replacing N_H along L gives a perfect matching

    N^+ = N_H symmetric-difference E(L).                   (4)

This is a written matching argument, not a matching search. No external augmenting-path theorem is needed: the degrees and alternation prove the claim directly. It supplies at least one repair of the endpoint deficits in each of the four rows. Simultaneous changes on any disjoint alternating cycles are permitted too; (4) is a sufficient way to repair degrees, not a restriction imposed on the target. There is no sequence of improvements here.

After repair, D^+=E(R) minus N^+ has degree one at all four terminals and degree two elsewhere. Thus it consists of two terminal paths and possibly closed cycles. The two paths' pairing is alpha or beta by the same complementary-disk argument, even if other components exist. Adding K_A is Hamiltonian exactly when there is no closed component and the pairing is beta. If the pairing is alpha there are two additional cycles through the patch; if there is a closed rest component it remains a separate component. These are exact failures of THIS direct candidate, not exclusions of other perfect matchings or all further reroutings. A closed rest cycle that passes through Y is not being claimed immune to exterior changes; only a closed X component has that immunity.

Even when the direct candidate is Hamiltonian, survival requires tracing its actual cut edges and local pairing and applying (S). The alternating path L is not proved contained in X, disjoint from Y, or disjoint from the five cut edges. Using all components of N_H symmetric-difference N_q would simply recover the known lost canonical matching N_q. Matching feasibility alone cannot establish survival.

Here is a useful conditional conclusion with no hidden type assumption. If a repair is confined to W=X-V_C, and D^+ has no cycle and pairing beta, it gives a canonical survivor of the SAME full type as H. The cut set and Y packing are unchanged. If cut 2 is used, (S) proves survival. If U=14, (S) again proves survival. For U=0134 the initial survivor has Y pairing 01,34 by the COMPLETE paid table; Hamiltonian connectedness forces the new X pairing to be 03,14, so it survives. Moreover at any four-port set both X and Y pairings are noncrossing in their respective disks. The only noncrossing choice different from the fixed Y pairing is the old X pairing, so the full type agrees. For two ports the pairing is unique. This proves exact type preservation, not an inference from local appearance.

The hypotheses do not currently prove the simultaneous conditions “repair inside W, no rest cycles, beta.” Nor do we prove they are necessary: a successful repair could change cut edges or Y and still satisfy (S). All such possibilities remain in the original existential quantifier.

### 4.3 Explicit one-edge repairs when the two unused terminals are adjacent

Suppose J'={u',v'} are adjacent by an edge f of R. Since they are unmatched in N_H, f lies in H_R. Delete f from the spanning rest path and add it to the matching. This is (4) with a one-edge path, so no other rest edge changes. The result consists of exactly two paths and has no rest cycle. Because u',v' lie in X, this operation keeps the cut edges and Y fixed.

For L_ab, deleting c'd' separates the a'-to-b' path into either pairing beta or gamma; alpha would put both old path endpoints in one of the two components, which cannot occur after cutting an internal edge of a path. Gamma is impossible by planarity, so the result is beta. Consequently adjacency c'd' proves canonical transport of ANY survivor in L_ab, preserving its full type by Section 4.2. For L_cd, adjacency a'b' proves the same conclusion by the identical endpoint argument: the choices are beta or gamma, hence beta. Both claims are conditional on actual adjacency, which is not one of the general hypotheses.

For L_bc, orient H_R from b' to c'. If f is traversed a' then d', deleting it gives pairs b'a' and d'c', namely alpha. If f is traversed d' then a', it gives pairs b'd' and a'c', namely beta. For L_ad, orient from a' to d'; traversing f from b' to c' gives alpha, while traversing it from c' to b' gives beta. These exhaust the two orientations of the edge on the path. In the beta cases the one-edge repair is a full-type-preserving canonical survivor transport.

In either mixed row's alpha case, the canonical candidate is exactly two cycles. If each uses two cut edges and their used set contains 2, the explicit exterior replacement in Section 3.3 reconnects them and gives a survivor, with the two local types in (3) interchanged. The proof applies verbatim: all cut edges and Y were fixed by the one-edge repair, so the local pairing after splitting equals the old Y pairing. If all cut edges lie on one component, the other is a closed X cycle and exterior-only repair fails. If U=0134 and the distribution is (2,2), the repair instead gives lost D. Thus even this fully specified degree repair has a concrete pairing/type dichotomy.

When the unused terminals are not adjacent, no one-edge repair is available. Longer matching repairs exist by Section 4.2 but their path coverage, pairings, cut use and possible cycle components are not controlled by the present argument. Failure of the short repair, or of a chosen longer repair, does not refute transport with an unrestricted change elsewhere.

### 4.4 General exterior-only completion boundary

For any proposed degree-two global candidate with canonical patch routes, hold its restriction to X and its cut-edge set fixed. If that restriction has a closed component, no change confined to Y can make it Hamiltonian. If it is cycle-free, trace its local pairing. An exterior completion changes neither that pairing nor U. The exact no-cut-2 table determines whether it is a lost or survivor row; for four-port sets using 2 the explicit witnesses in Section 3.3 supply the other pairing. For the two-port survivor types a compatible exterior exists by the given survivor Hamiltonian population (and for 14 it is explicitly S). Thus exterior replacement can finish a cycle-free canonical local survivor packing, but cannot convert a lost canonical local packing into a survivor. This boundary also covers candidates with a rest cycle that visits Y: those require the actual X trace, not automatic rejection based solely on the word “cycle.”

## 5. Complete disposition by patch class and original-target verdict

| Hamiltonian patch class | Settled transport or exclusion | Precisely unproved part |
| --- | --- | --- |
| K_A | Already canonical; every survivor gives E183 | None for this class |
| K_B | Hexagon replacement gives K_A with identical full type | None for this class |
| F, U=02,12,14,24 | Fixed-rest replacement creates a closed X component; exterior-only repair fails | A change of the rest inside X that supplies a canonical survivor, possibly changing U |
| F, U=0123,0234,1234, distribution (2,2) | Canonical split plus explicit Y rerouting gives a survivor, flipping the two local pairings | None for this subclass |
| F, U=0123,0234,1234, distribution (4,0) or (0,4) | Closed X component after canonical replacement | A change in X, rather than only Y, that avoids the closed component and yields a survivor |
| F, U=0134, distribution (2,2) | Explicit Y reconnection exists but yields lost D | A different X routing with survivor pairing, or a successful change of used set |
| F, U=0134, distribution (4,0) or (0,4) | Closed X component after replacement | A compensating X routing giving any survivor |
| L_ab | Degree repair exists; adjacency c'd' gives full-type-preserving transport | Without adjacency, an unrestricted repair with connected canonical complement and survivor type |
| L_cd | Degree repair exists; adjacency a'b' gives full-type-preserving transport | Without adjacency, the same simultaneous coverage/pairing/type requirement |
| L_bc | Degree repair exists; edge a'd' traversed d' then a' on b'→c' gives full-type-preserving transport; alpha with balanced four-cut set containing 2 is also settled by Y rerouting | Other short-repair subcases and general longer repairs: avoid closed X components, wrong rest pairing or lost type |
| L_ad | Degree repair exists; edge b'c' traversed c' then b' on a'→d' gives full-type-preserving transport; alpha with balanced four-cut set containing 2 is also settled by Y rerouting | Other short-repair subcases and general longer repairs: same explicit simultaneous requirements |
| Z,Z_top,Z_bottom | Excluded as Hamiltonian restrictions by their proper closed component | None; not candidate counterexamples |

“Unproved” in this table does not assert that an instance satisfying every E183 hypothesis realizes the obstructed subclass. It means the symbolic arguments do not exclude that subclass or provide its unrestricted survivor transport. Each failure is a proved limitation of the specified replacement, with the outstanding change identified; none is a universal impossibility theorem about other repairs.

To give the residual original-target obligation exactly, define for a perfect matching N of R the degree-two canonical candidate

    F_N = (E(R) minus N) union E(K_A),

where E(K_A) includes its four continuations. The following condition is NECESSARY AND SUFFICIENT for E183 on the given admissible instance:

    There exists a perfect matching N of R such that
    (i) E(R) minus N has no cycle component and terminal pairing beta;
    (ii) after tracing F_N in X, its type satisfies (S).        (T_R)

Necessity follows by deleting A from the desired matching and deleting the patch from its Hamiltonian complement. Sufficiency follows from (1), cubic complementation, and the exact survivor criterion. This ranges over ALL perfect matchings of R, not the fixed-root source image and not only one-edge or one-alternating-path repairs. There is at least one N satisfying (i), supplied by q (and separately by I188's nonempty image), but the known q witnesses type P rather than (ii).

The eleven complete nonempty survivor fibres supply cycles of every survivor type, but they do not yet ensure that one falls in a settled class or can be rerouted out of an open class. In particular, any admissible instance with no canonical survivor would necessarily have every survivor avoid K_A,K_B, avoid the balanced-cut-2 F subclass, and avoid the successful short-repair subclasses. Every survivor on such an instance would belong to an open row of the table. The present arguments neither construct such an instance nor prove this concentration impossible. Completeness of the fibres means every qualifying packing is present; it does not assert existence with an extra continuation prescription. No universal linkage between those complete fibres, the brace condition, and the good residual pairing/type in (T_R) is proved here.

**THREE-WAY VERDICT: UNRESOLVED.** E183 is neither proved via transport nor refuted. The canonical/toggled and the stated conditional transport classes are proved. The precise residual obstruction is simultaneous residual spanning-path topology and survivor port type after changing X for the open classes above. No fully hypothesized graph, complete fibre list for such a graph, or verified p,q counterexample is supplied. The displayed local patterns and exterior paths are not promoted into such an instance. Partial transport is not a full transport theorem.

## 6. Separation from the fixed-root source route

This analysis addresses I188's full population (17), exactly reformulated as (T_R). It does NOT pay I188's source-image implication (18). A transported canonical survivor, when one is supplied by a settled case, proves the target directly; no paired-state preimage is needed or asserted. To ask additionally whether its canonical state belongs to the fixed-root source image would require the I187 opposite-edge rooted-forest criterion, which is not verified here. This is only a scope remark. The nonempty marked image, its sign alignment and white-tree recovery remain available paid results, but were not used to assert survivor transport or surjectivity.

## 7. Proof, evidence and contribution limits

The original target retains every hypothesis and all eleven survivor alternatives. No cut-2 prescription has been introduced: use of 2 appears only as a sufficient branch of the exact criterion (S); no-cut-2 survivor 14;14 and 0134;03,14 are treated explicitly. There is no fixed completion or single-difference-cycle requirement. The one-shot augmenting-path argument is a conditional repair analysis, not a revived ear mechanism or an iterated improvement scheme. The parked local-ear route remains parked.

New written deductions here are the ten-row exhaustive restriction table; exact rest-pairing admissibility; lossless five-port tracing; the cut-distribution split analysis; explicit cut-2 exterior witnesses and their conditional transports; and the two-continuation matching-repair analysis with short-repair sufficient conditions. These are technical contributions, not a substantial-finding nomination. Eight accepted, two remaining; neither acceptance gate changes, and no new-to-literature theorem is claimed.

The retained manuscript was authenticated and its entire main TeX, lines 1–838, read, including the actual I188 operations. Its external figure, bibliography and PDF were not read. The focused catalogue/companion-path check identifies the relevant family, not an exhaustive priority survey. All pinned OpenAI results are stipulated true; there is no upstream truth audit and no separately invoked unread external theorem.

Validation is written mathematical checking of the degree equations, terminal parities, planar pairings, each explicit Y path and matching degree change. Document writing/reading and SHA-256 authentication are the only computational work. No research code, graph/state/matching scans or tests, experiments, historical replay or control rebuild, source copies, snapshots/seals, further agents, ancestor/shared-ledger edits, staging, commits or publication occurred. This is an unsealed proof record, not independent review or proof-assistant verification. The inherited 23-stage replay and twelve facial/626 matching controls were not rerun. No sequel or implication for Z184, exchange, (T), Q164 or earlier targets is claimed.
