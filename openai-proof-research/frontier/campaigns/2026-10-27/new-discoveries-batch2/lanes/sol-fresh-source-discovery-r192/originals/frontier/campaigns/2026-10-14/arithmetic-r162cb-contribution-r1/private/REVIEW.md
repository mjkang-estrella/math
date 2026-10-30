# R162CB independent full-scope contribution review — round 1

**Verdict: TECHNICAL, conditional on correctness of the entire unchanged frozen theorem.** This is a contribution judgment, not a correctness verdict. No correctness PASS, acceptance, count, or priority claim is made. No other review was inspected.

The reviewed statement has SHA256 `b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a`; the reviewed author proof has SHA256 `c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e`. The quantifiers are all sufficiently large eligible primes s, followed for each s by every sufficiently large odd n, with q=s^n and r=q+1. The conclusions are simultaneously: a finite simple r-partite r-uniform hypergraph, exactly r nonisolated vertices in every part, every pair of distinct edges meeting in one or two vertices, and integral cover number r. None is dropped in this comparison.

## 1. Basis of the judgment

The entire extension source proof already provides a single configuration with exact local resource bounds, not merely an existence theorem for its cover number. The balanced companion already provides the operation of merging blocks while representing each merged block by one line on a common core, then forcing a pencil and accounting for the additional action of its partners. In the extension configuration, the omitted lines give a direct specialization of that mechanism. Its verification requires only the source's existing separation, omitted-line incidences, two-axis rigidity, and degree-three intersection estimate. All the adjustments fit the margins of the same source cover proof. There is no new incidence theorem, random event, independent-transversal construction, selection law, or asymptotic parameter negotiation.

This is not the assertion that arbitrary mergers preserve cover number, that balance alone implies the theorem, or that the balanced prime theorem applies literally at s^n. The technical payment is the explicit common-configuration reduction in Sections 3–6 below. The source deterministic proposition has four-point tuple hypotheses; the present reduction does not falsely claim that those tuples are present. It uses the actual proof operation and verifies its local consequences in the extension configuration.

The omitted-line choice is useful. Its usefulness does not by itself create an additional nonroutine operation: the lines already belong to the stipulated gadget, their pairwise intersections are determined by a two-by-two system over F_s, and their extra label actions are handled by the exact source cubic bound and integer resource margins. The full joint argument, rather than the elementary nature of any isolated ingredient, is what supports TECHNICAL.

## 2. Strongest source interfaces credited

Both actual `build/paper.tex` wrappers and all their operative mathematical includes, figures, elementary estimates, and bibliographies were read completely. The two source PDFs were authenticated but not visually read. Source truth is stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

For the balanced source, the paid content includes its finite-field deterministic reduction (`construction.tex`, `prop:deterministic-reduction`), core representatives for merged blocks, forced nonsplit pencil members including a removed constituent, all b=0,1,2 and b>=3 local-cover cases, tuple generation and compatibility, moment counts, exceptional codegrees, equalized selection and stopping/censoring, occupancy, full cylinder bounds, independent-offset integration, local incidence enumeration, and the robust prime-power profile/change-of-measure deletion theorem. Only the concluding Szonyi–Weiner application there is prime-specific. Its final prime theorem, nonisolation and tree-cover consequences are fully credited.

For the extension source, the paid content includes its uniform finite-field incidence bound and simultaneous difference/quotient extraction, scalar covering and subfield exclusion, independent-trial line-cover theorem including almost-covers, candidate-pool selection, separation and occupancy transfer to the selected copies, and the complete small-plane gadget and final cover proof. In particular, the exact operative labels are `lem:gadget`, `con-deletion-count`, `con-pool-properties`, `con-separation`, `con-selected-line-bound`, `con-exceptional-vertex`, `con-label-action`, and `con-forced-pencil` in `construction.tex`, with their full proofs. The original construction's implicit linearity and exact q+z_d active-label counts are paid as direct readings of those rules.

One cannot simply substitute the extension line-cover theorem for the balanced source's prime stability step without checking its deletion-law hypotheses: the former assumes common independent trials, while the latter selection is controlled by exponential domination. That alternative transfer is not needed here and remains unasserted. Its unproved compatibility is not evidence for SUBSTANTIAL and is not an essential gap in the completed reduction below.

## 3. Fixing one source configuration and performing the quotient

Fix a sufficiently large prime s congruent to 2 mod 3 and the source gadget Y in F_s^2. Its omitted line in each nonzero finite slope t is ell_t. Every other line of that slope has at least five Y-points. Under f(x,y)=(x^3,y), every line meets f(Y), and any mixed cover of f(Y) with a lines and b points and a+b/2<=s must consist of the s lines of a full parallel class. In particular, fewer than s lines cannot cover f(Y), and at most s lines containing the two nonparallel axes cannot cover it. The source gadget proof already proves that a nonaxis original line, transformed by f, meets any nonaxis line in at most three points by a cubic equation.

For one eligible n, retain one complete successful source pool and selection at q=s^n. All its constants, shifts, copies, deletions, and ordinary survivors stay fixed for the entire argument. Write

- P_i=b_i+M_i(F_s^2), Y_i=b_i+M_iY;
- S_i for its changed directions, A_i for its two axis directions;
- B_i for the changed-direction ambient lines meeting Y_i, B=union B_i;
- X=F_q^2 minus the union of B.

The indices are the representatives lambda of F_q^*/F_s^*, including 1, and the extra index *. The source has M_1=identity, S_1=F_s^*, and S_* = P^1(F_s) minus {u,v} for distinct nonzero u,v. Every direction belongs to z_d=1 or 2 of the sets S_i. Precisely T=F_s^* minus {u,v} has z_d=2, with the two groups always 1 and *. Thus |T|=s-3. The conflict directions of groups 1 and * include all of P^1(F_s).

Separation says that any line of direction in D_i meeting P_i misses every other P_j. Every d in S_i contributes exactly s-1 distinct deletion lines. Occupancy gives at least delta*q/2 ordinary points on every line not in B. On removing isolated vertices, the original direction part therefore has exactly

    q - z_d(s-1) + z_d*s = q+z_d

vertices. The special labels are all active because every line meets f(Y). No exceptional edge uses an ordinary deletion-line label: its own group changes that direction and other groups miss the line. Conversely every nondeleted ordinary label is active by occupancy. Hence the count is exact, not an upper bound.

For each d in T, let O_d=b_1+ell_d extended to the ambient plane, and choose any one group-1 special label v_d of direction d. There is no coordinated choice or extra existence theorem for v_d. The line O_d misses Y_1, and separation makes it miss every other P_i. It belongs to no B_i and its ordinary label is active. No exceptional edge of any group contains its ordinary label.

Two different O_d have different directions and intersect inside P_1: after subtracting b_1 their two line equations have coefficients in F_s and a nonsingular coefficient matrix. This incidence fact holds for all the chosen omitted lines at once.

In each d in T identify the two vertices o_(O_d) and v_d, with no other identification. These pairs lie in different parts, so the identifications are disjoint. Let H be the image hypergraph and m_d the merged vertex. Its parts remain disjoint, every edge has one vertex in each part, and every part has q+1 vertices. Each resulting vertex is active. A merged vertex has exactly one ordinary representative, namely O_d, and its action on exceptional edges is exactly its group-1 special action. Distinct labels with ordinary representatives have distinct representative lines.

This is one quotient of one hypergraph. No rank lift, change of ordinary survivors, deletion of extra edges, or separately optimized configuration occurs.

## 4. All quotient covers on that configuration

Suppose a cover C has at most q vertices. Replace every selected vertex having an ordinary representative by its representative line. These distinct lines cover X. By `con-pool-properties(i)`, which transfers from the same pool because X contains X_pool, at least (1-rho)q representatives pass through one projective center p, where rho=delta/10.

Every nondeleted line through p is forced: if its label were absent, all the other pencil representatives together would cover at most the point p on that line, and the at most rho*q other labels would cover at most rho*q further ordinary points. Special labels cover none, and each merged label still has only one representative. This contradicts delta*q/2>1+rho*q. Thus let F_p contain the forced quotient labels of all nondeleted pencil lines. They are distinct.

The only action on exceptional edges gained over the original source F_p is one group-1 special line for each O_d through p. Denote their number by a(p). A merged label outside F_p still acts on exceptional edges only as its original group-1 special label. This observation verifies the capacity of every additional label, not just those in a preferred cover.

### 4a. Center at infinity

If p is the point of direction g, exactly z_g(s-1) lines in that parallel class are deleted, leaving q-z_g(s-1) forced labels and at most z_g(s-1) additional labels.

For z_g=1 there is no free special line: only a merged representative of direction g could lie in this infinite pencil, and that direction is not doubled. The affected group would be covered by at most s-1 additional small-plane lines using `con-label-action`, impossible.

For z_g=2 the affected groups are 1 and *. There is exactly one free special line. Use the source's two-group cost: a special label or an ordinary axis line meeting a group costs one line there; an ordinary nonaxis line contributes at most one point of weight 1/2 to each group. An axis line meeting one group misses the other by separation. Each additional label therefore contributes at most one in total across both groups. This is also true of any merged label, whose exceptional action is just one group-1 line. Each group requires cost at least s, but

    2s <= total resource cost <= 2(s-1)+1 = 2s-1.

The existing deficit of two tolerates the one free resource. No uncharged fractional-cover assertion is used: these are actual covering lines and points counted at the gadget's stipulated costs.

### 4b. Finite center inside P_i

Let h=|{ell in B : p in ell}|. There are q+1-h forced labels and at most h-1 additional labels. If h=0 the forced count alone is impossible.

When p lies in P_i, separation makes every deleted line through p come from that group, and h<=s-1. The ordinary components of forced labels cover that group's exceptional points only on its two transformed axes through f(M_i^(-1)(p-b_i)). Each additional label can be enlarged to one small-plane line, including singletons.

For i different from 1, every O_d misses P_i, so there are no free resources. The original source bound is unchanged: at most 2+(h-1)<=s lines including the two nonparallel axes would cover f(Y).

For i=1, put a=a(p). Each free resource uses a distinct changed direction whose line through p is omitted, and hence not deleted. Every deleted pencil line uses a different changed direction. Therefore the exact elementary budget is

    h+a <= |S_1| = s-1.

The two axes, the a free special lines, and the at most h-1 additional resources would cover f(Y) with at most 2+a+h-1<=s lines containing two nonparallel lines. Removing duplicates preserves those two distinct axes. The same source gadget excludes this cover. This charges all simultaneous mergers, even if many O_d concur inside P_1.

### 4c. Finite center outside every P_i

Each group contributes at most one deleted line through p, because two distinct such small-field lines intersect in P_i. Choose the source's same five exceptional witnesses on each contributing line, for a total of 5h distinct edges before quotienting. Distinctness after quotienting follows from Section 5 below. No ordinary component of a forced label covers them, by the unique-join argument and the changed direction.

There is at most one O_d through p because two intersect in P_1. Thus there is at most one free special resource. It affects witnesses only in group 1. If that group contributes a deleted line y=t x+c, then t is nonzero. A chosen special line of slope d in T has transformed equation Y=dX+b, so intersection with these witnesses requires

    d x^3 - t x + (b-c) = 0.

This is the very degree-three bound already proved in the source gadget, and d is nonzero. It covers at most three of the five witnesses. No new polynomial method or additional configuration is involved.

Every additional label covers at most five witnesses. Special or merged labels are confined to one group of five. An ordinary line through p covers none. An ordinary line not through p covers at most one per contributing group, and `con-pool-properties(iii)` bounds those groups by five on this same selected configuration. Therefore total coverage is at most

    3+5(h-1) = 5h-2 < 5h.

All projective centers are now excluded. Consequently the quotient has no q-cover. Any direction part of size q+1 is a cover, so its cover number is exactly q+1.

## 5. Intersection cap and simplicity on the same quotient

The original extension hypergraph is linear, directly from its label rules. Two ordinary edges share only their join label. An ordinary and an exceptional edge share only their join label, whose direction cannot be changed for the exceptional group because X avoids its deletion lines. Two different exceptional groups share only their ordinary join label; special labels are group-tagged and separation puts the join outside both changed-direction sets. Within one exceptional group, a common ordinary label can only be an axis label. The bijection f preserves both axis parallel classes; if the transformed join is an axis, that is the unique common label, and otherwise the transformed nonaxis join gives exactly one special label and there is no common axis label. These arguments also show the original edges are distinct.

An ordinary survivor cannot lie in any P_i. If p=b_i+M_i a survived there, each nonaxis small-field line through a would have to be its direction's omitted line. Otherwise its ambient extension contains Y_i and is deleted. Thus all s-1 omitted lines would pass through a and Y would lie in the two axis lines through a. Applying f preserves those axes and would cover f(Y) by two nonparallel lines, contradicting the source gadget for s>=7. Hence X avoids every P_i.

It follows that an ordinary point of X lies on at most one O_d, since two of them intersect in P_1. No exceptional edge contains any of their ordinary labels. Among ordinary edges the quotient is only injective renaming of ordinary labels; among exceptional edges it is only injective renaming of selected special labels. Those pair types acquire no new intersection. An ordinary edge and an exceptional edge can acquire at most one common merged label, and only for group 1. Their original common label remains common. Thus for every pair of distinct original edges,

    1 <= |image(e) intersect image(f)| <= 2.

Every image still has r=q+1>2 vertices, so two different original edges cannot have equal images. H is therefore simple, and the cap holds for all its distinct edges. The conclusion does not rely on choosing a separate linear or balanced witness.

## 6. Quantifiers and payment of every conclusion

Choose s_0 at least 7 beyond the source gadget threshold. For every prime s>=s_0 with s=2 mod 3, fix one source Y. Fix the source constants in their prescribed order; no constant is chosen in response to a hypothetical cover. For every odd n beyond the source threshold and delta*q/2>1+rho*q, retain one successful source placement and apply the deterministic quotient above. Enlarge n_0(s) to at least 3 if necessary. All subsequent assertions hold for every such odd n, with q=s^n, without requiring a new event or restricting to a subsequence.

Finite vertex and edge sets come from the source construction; the quotient preserves finiteness. Partwise identifications preserve one vertex per part and rank r. Exact q+z_d counts and one merge in each doubled part give r active vertices in every part. Section 5 gives simplicity and intersections in {1,2}; Section 4 gives tau=r on that very quotient. Thus this is payment of the entire unchanged conclusion, including the extension-order quantifiers, not separate witnesses for subsets of it.

## 7. Actual primary constructions compared

These comparisons are based on the proofs read in the admitted primary copies, not their abstracts or author notes. They credit useful operations without asserting that one route's limitations are universal obstructions.

### Haxell–Scott: affine skeleton and matching-coupled variant

The complete nine-page author-hosted paper was read. In Sections 2–3, A_p is obtained by removing a point and all its incident lines from AG(2,p). It has p+1 sides of size p-1, p-uniform skeleton edges, and p-1 disjoint edges in each parallel class. Their construction attaches a disjoint copy J_i and takes all e union f with e in class i and f in J_i. Intersection is supplied by skeleton intersections between classes and by J_i within a class. Their minimum-cover argument forces a cover touching J_i to cover J_i, or else exposes an uncovered product edge.

The actual lower comparison is the minimum of 2p-2 (pure skeleton), p-1+tau(J) (mixed case), and (p+1)tau(J) (all gadget copies), under their rank assumptions. Substituting a maximal-cover input does not turn p-1+tau(J) into p+tau(J). More directly, the construction retains repeated skeleton edges: two distinct e union f and e union f' share all p skeleton vertices. At large p it cannot give the required cap two without another operation. The matching-coupled Section 5 construction uses J from AG(2,p-1), matches parallel classes, and replaces gadget portions of a minimum cover by p-1 skeleton points. It has rank 2p-1 and cover 2p-2; edges with the same e again share p vertices. Both full operations are paid. Their precise limitations do not support a substantial verdict; the completed quotient route already pays the target.

### Abu-Khazneh–Barat–Pokrovskiy–Szabo: exact exceptional-edge construction

The complete eleven-page v2 paper was read. Theorem 1.2 assumes an edge S meeting every other input edge once, tau(T-S)=r-1, and all size-r-1 covers of T-S being sides. Section 2 forms E-hat=E+v_i, includes each F_i, and includes F_i-s_i+v_i. Lemma 2.2 replaces any chosen v_i by s_i to produce a cover of T-S; the minimum-cover rigidity then gives the contradiction in Theorem 2.3. This is an (r+1)-partite mixed {r,r+1}-uniform example with cover r, made uniform by private padding.

All of this representative-cover mechanism, the truncated-plane minimum-cover lemma, and the minimal/maximal example operations are credited. The actual exceptional pair F_i and F_i-s_i+v_i has intersection r-1, which padding cannot remove. Also F_i remains an r-cover of the intersecting output, even after padding. Thus it is not a maximal-cover cap-two rank lift for large r. This is an explicit structural comparison, not a claim that a different exceptional construction is impossible.

### Francetic–Herke–McKay–Wanless: linearity and MOLS

All sixteen pages of arXiv:1508.00951v3 were read, including their restrictions, constructions and computational descriptions. The rank-13 cyclic example has exactly thirteen active vertices per part and is linear, but the paper supplies a nine-cover and reports cover nine. Lemma 3.3 from k MOLS of order m builds rank m+2 with cover k+1<=m, not m+2. Its explicit cover uses levels of one side plus an additional vertex; no side or edge-subset need be a minimum cover. The H_38 construction is rank eight, linear and cover seven; the cyclic nonlinear examples have cover r-1. The low-r degree arguments and enumeration are not infinite-rank construction interfaces. No program was rerun here. Balance, nonisolation, and linearity are credited as known properties, with their actual cover numbers; they cannot be combined with a separate source cover witness by identification without a cover argument. Sections 3–6 above give that argument directly instead.

### Bucic–Jain–Sivashankar: strongest wreath and augmentation reading

All nine pages of arXiv:2503.14918v2 were read. Lemmas 3–5 give rank multiplication, intersection, and exact integral cover multiplication for the wreath product, with full choice of an inner edge independently at each vertex of an outer edge. For multipartite factors, grouping vertices by the pair of part indices gives a legitimate product part system. Balanced factors with part sizes equal to their ranks yield balanced products, so that compatible strengthening is credited, not omitted.

However, for r_1,r_2>=2 and an inner hypergraph with at least two edges, hold one outer edge fixed and change only one inner choice. Two resulting distinct product edges share at least (r_1-1)r_2+1>=3 vertices when the inner hypergraph is intersecting. Thus the full nontrivial wreath does not preserve cap two, even though its cover and balance conclusions are strong. The one-edge inner exception is not a maximal-cover factor of rank at least two.

Lemma 8's augmentation retains all e+v for v in a new set S of r+1 vertices and also adds S. It has cover r+1, exactly as proved there, but e+v and e+w share r vertices. Moreover the obstruction to (r+1)-partiteness is stronger than failure of a fixed old part system: in ANY proposed (r+1)-part system one old e occupies r distinct parts, so every v in S must occupy the one remaining part because all e+v are edges. The edge S would then contain r+1 vertices in that part, impossible. This argument checks arbitrary repartitions of the actual output. It does not rule out other constructions. The complete nonpartite vertex/edge-count theorem and its padding are credited, but no unsupported partite transfer is made.

### DeBiasio–Kamel–McCourt–Sheats: component equivalence and merging

PDF pages 1–8 and 50–51 were read, including the complete Appendix A proof. Section 1.2 associates vertices with monochromatic components and edges with their simultaneous occurrences. Conversely the partite hypergraph produces an edge-multicolored intersection graph with color components cliques. Keeping the component partitions keeps that dual hypergraph. This pays the encoding, not arbitrary coarsening of a partition while keeping its cover number.

Appendix A's Theorem 9.1(v) merges two GRAPH vertices in the intersection of the same r components. Those graph vertices represent duplicate hyperedge incidence patterns; a cover of the merged graph lifts because every component through the merged vertex contained both original vertices. It does not merge two different components, which would correspond to identifying two hypergraph vertices and could lower tau. Its lexicographic minimal-counterexample hypotheses likewise cannot be silently imposed on this fixed rank configuration. All the stated minimality conclusions at the read scope are credited. No hypothesis of them is used to pay the quotient. Pages 9–49 were not semantically read; their bounded-diameter and other generalizations are not premises of the reduction.

### Szonyi–Weiner: actual prime-plane stability proof

The complete eight-page July 18, 2014 author manuscript was read. Theorem 2.4 uses a Redei polynomial, an auxiliary polynomial vanishing on the skew-line parameter set, a degree comparison, and the vanishing-derivative case where q=p is essential. The source's prime-plane pencil consequence is paid with the actual prime restriction. No extension to s^n is presumed. The extension source already supplies its own stronger compatible independent-trial incidence/pencil argument at the retained orders, and that is the input used above.

## 8. Remaining obligations and limits

There is no unresolved mathematical bridge in this contribution reduction conditional on the entire theorem's correctness and the stipulated operative source truth. The independent correctness review remains outside this role; no inference about its status or result is made. Artifact verification supplies no mathematical gate.

This review does not establish literature priority or exhaust all ancestry. The six named primaries were read at the extents recorded above; transitive references such as original finite-plane blocking, sum-product, concentration, independent-transversal and random-line papers were not separately read in full. Their applicable operations are credited through the complete stipulated source proofs. No optional project-history traversal, completed prior-round body, correctness-review input, foreign status, or containing-namespace expansion was used. These limits do not create an essential unpaid comparison for a TECHNICAL verdict because a complete compatible source reduction has been given. They would prohibit a worldwide novelty assertion, which is not made.
