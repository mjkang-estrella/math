# First independent contribution review of the entire frozen S176A

**Contribution verdict: TECHNICAL, conditional on correctness of the entire unchanged statement.** This is not a correctness PASS, an acceptance, or a count. The statement and author proof retain their supplied SHA256 identities. Every graph order, graph class, output condition, probability quantifier, and Turing-bit bound remains in scope.

The decisive comparison is constructive, not an appeal to the existential headline. Source181 pays the multiscale vertex savings, assigned-edge accounting, reservoir sampling, and simple-cycle lifting. Its apparent algorithmic bottlenecks can be discharged by its own DFS proof, the saturation method in Conlon–Fox–Sudakov (CFS), the original finite Lovász reconstruction, and standard rational optimization. In particular, **Leighton–Rao's actual uniform sparsest-cut rounding proof gives a polynomial replacement for expanding-piece extraction with residual degree O(D^.90 log² D), which fits the source's original D^.95 budget.** The author's D^.98 spectral loss and larger scale gap are therefore not an indispensable surviving operation. The calculation below integrates these replacements with the complete part-count and expected-time requirements.

This alternative derivation is a contribution comparison at the same theorem, not a repair of AUTHOR-PROOF.md, a new nominee, or a restriction of S176A. No independent correctness sibling was read. No author response or previous review is used.

## 1. Scope, dependencies, and what must actually be constructed

Input is the binary adjacency matrix of an arbitrary simple undirected graph on [n], including n=0, disconnected graphs and isolated vertices. Output parts must be explicit simple cycles of length at least three or original single edges; they must partition all original edges. The part bound holds on every terminating execution. Almost-sure termination and expected polynomial Turing-bit time use uniform absolute integer constants and fair bits.

All nine canonical Source181 objects at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb were authenticated against the complete tree and read in full: main, preliminaries, routing, residue, splitting, folding, induction, the lifting figure, and references. Their truth and operative upstream proofs are stipulated, not audited. In particular, the following source interfaces are already paid:

* `lem:scale-split`: overlapping boxes covering all vertices, order overhead 1+2/log D, long-cycle charge N/(2D^.01), and vertex-disjoint expanding pieces inside each indexed box.
* `lem:vertex-sampling` and `lem:small-residue`: arbitrarily small fixed reservoirs, bounded representative loads, at most 9r completed parts, and residual total order at most eta r.
* `lem:pair-folding` and `lem:batch-resolution`: unique representatives, exact quotient orders, global per-box endpoint loads, team constraints, and one simple lifted cycle per quotient cycle.
* `lem:prefix-choice` and `prop:induction-bound`: the prefix charge, savings of S/3 quotient vertices, residual order S/100, and the inverse-square-root-log potential.

These are much more than the existence of an O(n)-part partition. The comparison below uses their actual proof operations. It does not assert that an arbitrary existential decomposition theorem can be implemented efficiently.

## 2. The classical path primitive, including its finite reconstruction

The original Lovász paper was accessed independently through the web PDF reader, whose four scanned sheets expose the original definitions, Theorem 1, and proof at lines 36–157. Direct download and two explicit alternate download attempts each returned 403. A screenshot request returned only a reference, with no visible image. The original OCR is damaged at some subscripts and in the successor-sequence sentence. I do not certify a legible scanned-image reading. The following is an explicit reconstruction of the finite operation visible in that proof; it resolves the computational interface rather than treating damaged OCR as an algorithmic certificate.

Let e be the edge count and a the number of nonisolated vertices. Recursion is on lambda=2e-a. At lambda=0 the graph is a matching plus isolated vertices. Otherwise choose a nonisolated even vertex y and its neighbor x, if one exists. If all nonisolated vertices are odd, choose x of degree at least three and subdivide one edge xz by a new y. Write G1 for the resulting graph. Delete all edges from x to the even neighbors of x in G1 to obtain G'.

Without subdivision, k>=1 edges are deleted and only x can become isolated: every affected neighbor had positive even degree and now has positive odd degree. Thus lambda(G')<=lambda(G)-2k+1<lambda(G). With subdivision, y is the sole nonisolated even vertex, xy is deleted, e(G')=e(G), and a(G')=a(G)+1; again lambda falls by one. There is one recursive call, its edge count never increases, and there are at most 2e calls and O(n+e) vertices.

Here is the explicit local reconstruction, making the damaged indices unnecessary. Let H=N_G1(x). Every vertex of H is odd in G', so choose for each v in H one returned path P(v) having endpoint v. Fix these choices. Start a chain at every even neighbor a_i of x in G1 (precisely the missing x-edges). From a current v, stop if P(v) avoids x. Otherwise let the successor be the neighbor of x on P(v) on the side toward endpoint v. This successor belongs to H and is joined to x in G'.

These chains have no collisions or repetitions. A successor w identifies the unique returned path containing edge xw. Within that path, traversing from x through w recovers the endpoint that produced the successor. If both endpoints of that path occur in H, they produce different neighbors of x; if x is an endpoint only the other endpoint can be in H. Thus the predecessor is unique. Starting vertices have no x-edge in G' and cannot be successors. A repetition would trace backwards to a starting vertex having a predecessor, a contradiction. The total number of chain vertices is at most |H|. In particular the apparent case P(v)=vx, which would be a self-loop successor, is unreachable from a starting vertex: its edge would already have belonged to the distinct predecessor path.

Let H' be the union of these chains. Modify each returned path P only once. If neither endpoint is in H', leave it unchanged. For each endpoint v in H', add xv; if P contains x, also remove the edge incident with x on the side toward v. With one selected endpoint this is a simple path. With two and x internal, it is again a simple path, obtained by reconnecting the two end segments through x. With two and x absent it is a simple cycle. Returned cycles are unchanged. All vertices used on each new path or cycle are distinct. Each missing x-edge at a chain start is added once. Every other chain x-edge is deleted once from its predecessor path and added once to its endpoint path. All other edges retain their unique owner. Thus this operation preserves the number of parts and partitions E(G1).

In the subdivision case the a old nonisolated vertices are odd and a is even. A decomposition with at most floor((a+1)/2)=a/2 parts must consist of paths and must use each old nonisolated vertex exactly once as an endpoint. Hence y is not an endpoint; suppressing x-y-z in its path restores xz and keeps the path simple. All auxiliary vertices are removed while unwinding. Everything is scanning paths, degrees, and adjacency tables, with polynomially many operations on O(log(n+e))-bit indices.

Finally apply the parity augmentation actually proved in Source181 `cor:endpoint-paths` and BM Corollary 22. Add v0 adjacent to each even-degree old vertex. All old vertices become odd. The part bound forces paths only and exactly one old endpoint occurrence each. Deleting v0 creates at most one additional endpoint occurrence at any old vertex. The result has endpoint load at most two and at most n positive-length simple paths. Empty graphs give no paths. This supplies the precise polynomial primitive; a generic path/cycle existence statement alone would not have supplied it.

## 3. DFS already gives the cycle-or-separator search

BM Lemma 25 and Source181 `lem:split-vertex-expansion` actually run DFS, balance unexplored and finished vertices, split the stack into three intervals, and search for a bypass. Their proof can return the obstruction when an expansion inequality fails.

For u sufficiently large put alpha=1/(32 ceil(log2 u)^2), q=alpha²u/100. A disconnected graph supplies a component U of order at most u/2 with empty external neighborhood. In a connected graph stop DFS when the unexplored and finished counts both equal t; the stack is a path of order L=u-2t. Such a state exists since their difference falls by exactly one at each operation.

If L<alpha u/3 then t>u/3, and the unexplored set is a valid U, with boundary contained in the stack and smaller than alpha t. Otherwise split the stack into X,J,Z with |J|=floor q and |X|,|Z|>=L/4. For the fixed large cutoff, floor q>=1 and floor q+1<=L/2, so all rounding is valid. BFS in H-J either finds a shortest X–Z path, whose interior avoids the entire stack and closes a simple cycle of length >=floor q+2>q, or fails. In the latter case choose the smaller of the component containing X and all remaining components. Both sides contain at least L/4 vertices, and the chosen side has external neighborhood contained in J. Since |J|<=alpha²u/100<alpha L/4, it is a valid separator.

For u>D^1.02, q(u)>D^1.01 uniformly above an absolute cutoff; the ceiling loses only a fixed factor and u/log⁴u is eventually increasing. Interleave cycle deletion and overlapping splitting, retaining the current vertex set after deletion. At most ND/(2D^1.01) cycles are deleted. At every split the overlap is less than |U|/(32 log²u), so the source's exact potential `eq:split-potential` and its subadditivity calculation apply unchanged. Leaf order sum is at most N(1+2/log D). This does not need a maximal family of long cycles, a longest-cycle oracle, or the unnecessary assertion that each final box contains no long cycle. There are O(N) splits and at most |E(G)| cycle deletions.

This is extraction of witnesses from the actual paid DFS proof, not a new long-cycle theorem.

## 4. A stronger standard cut operation removes the claimed spectral necessity

Leighton–Rao, JACM 46 (1999), Sections 2.2 and 3.1–3.2, give the needed operation for uniform demands. I read the actual distance-LP setup and the proofs of Lemma 3, Corollary 4, Lemmas 5–6, and their sparsest-cut/flux application; the selection is retained privately. Their two alternatives are low-radius regions yielding a balanced cut, or a large region whose distance layers yield a low-ratio cut. No all-pairs disjoint-path or hypergraph algorithm is being inferred from their title.

Here is the exact interface, with its bit-model details. For a connected u-vertex simple graph solve the rational LP with variables d_vw>=0 for unordered distinct pairs, triangle inequalities, sum_{v<w}d_vw=1, minimizing W=sum_{vw in E}d_vw. It has O(u²) variables, O(u³) constraints, and integer coefficients of bounded size. Standard polynomial-bit rational linear programming returns an optimum of polynomial bit length. Connectivity implies W>0. The shortest-path distances of the edge lengths d_e dominate the LP metric and so still have pairwise sum at least one. A normalized cut metric is feasible, hence

    W <= min_A |boundary A|/(|A|(u-|A|)) =: Phi_*.

If a zero-length edge is inconvenient, replace every edge length by d_e+W/m, where m>0 is the edge count. Total weight becomes W'=2W; the distance constraint persists. All edge lengths are positive rational numbers. This only loses a factor two.

The actual region-growing proof is polynomial in this unit-capacity setting: its auxiliary graph replaces edge e by ceil(m d'_e/W') edges, whose total is at most 2m. Thus it does not conceal exponentially many subdivisions of a tiny or enormous rational length. Its thresholds use rational distances, integer ceilings, and L=ceil(log2(2u)); replacing log u by L in the proof only enlarges the explicit constant. Lemma 3 yields cut capacity <=4W'L/Delta and radius <=Delta. At Delta=1/(2u²), Corollary 4 yields ratio cost <=36W'L unless there is a region T of at least 2u/3 vertices. For that region, sum_{v outside T}dist(T,v)>1/(2u), and Lemma 5 finds a layer cut of ratio cost <=6W'. The sweeps have polynomially many layers. Consequently one obtains an explicit cut with

    |boundary A|/(|A|(u-|A|)) <= 72 L Phi_*.

For h_*=min_A |boundary A|/min(|A|,u-|A|), we have u Phi_*/2<=h_*<=u Phi_*. Therefore the returned cut density d(A)=|boundary A|/min(|A|,u-|A|) satisfies

    d(A) <=144 L h_*.

Use the conservative integer factor A(u)=512 ceil(log2(2u)). A disconnected graph instead supplies a zero cut by components. The comparisons, including equality, are rational and exact.

In a source box Y of order y<=D^1.02, set s=ceil(D^.90). On each nonsingleton current graph run this cut algorithm. If its returned cut has d(A)>A(u)s, the approximation guarantee proves h_*>s, so retain the graph as an expanding piece. Otherwise put the cut edges in the residual and recurse inside both sides. The terminal pieces have expansion at least D^.90 and order at least D^.90; their vertex sets are disjoint subsets of Y. The full Y remains the residual vertex set.

Each vertex is on a charged smaller side at most log2 y times. Since A(u)<=512 ceil(log2(2y)), the total residual degree is at most

    2 A(y) s log2 y = O(D^.90 (log D)^2) <= D^.95

above a fixed absolute cutoff. Every cut is found in polynomial bit time, and there are at most y-1 splits. This supplies exactly the expansion, residual-degree and vertex-retention interface needed by Source181; it is stronger than the author's D^.98 variant.

The author's spectral replacement is also an elementary alternative: rational congruence elimination for L_H-2s(I-11^T/u), centering, median splitting, and the threshold identity yield cut density <2 sqrt(Delta s)<=3D^.96. Smaller-side charging gives residual degree O(D^.96 log D)<=D^.98. The operation uses a familiar sweep inequality with an explicitly affordable power loss. In the contribution comparison it cannot be an unavoidable nonroutine bridge because the standard LP cut operation above preserves the stricter source budget.

## 5. CFS saturation fits both actual routing uses

CFS Lemma 5.1 actually routes greedily while prohibiting vertices after a bounded number of internal uses; it bounds incident used edges by twice that internal cap plus endpoint load. Source181's cut-ball argument supplies the short-path existence once these deleted resources are small. Team restrictions add only the previously used interiors of that team.

More explicitly, let P have order r and cut expansion at least a rational h, each vertex at most k demand endpoints, team size at most b, and forbidden interior sets of size at most z. Let

    L=ceil(32(r/h) ceil(log2(2r))), t=floor(h/16).

Assume h>=32, k+2<=h/8, and

    16krL/h + z + bL <= h/4.                         (R)

Prohibit a vertex internally after t internal uses; endpoints are retained. Used incident edges number at most 2t+k<=h/4. There are at most kr/2 demands, so at most 16krL/h saturated vertices. Add the current forbidden set and earlier team interiors to get W of size at most h/4, excluding the endpoints. Simplicity gives, for any remaining U of size at most r/2,

    boundary_(P-F-W)(U) >= h|U|-(h/4)|U|-|W||U| >= h|U|/2.

Balls grow by factor at least 1+h/(2r) until larger than r/2. Two endpoint balls intersect after O((r/h)log r) steps. BFS therefore returns a simple route of length at most L. All steps and the route certificates are polynomial.

In batch lifting r<=D^1.02, h is a fixed multiple of D^.90, k=D^.01, b=D^.30, z=2D^.30. The saturation term is O(D^.25 log D), and the team term is O(D^.42 log D), both smaller than h. In reservoirs h is a fixed multiple of D^.74, r_i<=r<=D^1.02, k=O(r/D^.90), b=1, z=0. The saturation term is O(D^.68 log D), smaller than D^.74. These are the two regimes actually needed. This comparison does not assert a polynomial algorithm for all parameters of Source181's more general hypergraph routing lemma or BM's weakest robust expanders.

The load is global across all batches of a fixed earlier box, not separately reset per batch. The actual source injection assigns each remnant endpoint its terminal original edge and each switch endpoint its retained representative incidence. These edges are distinct in F(Y), giving total load <=d_F(x)<=D^.01. Thus the number of batches does not multiply k.

The source's full lifting proof remains operative: different visited quotient fibers are disjoint; each route interior avoids all representative endpoints; interiors within a cycle's team are disjoint; different routers inside a box have disjoint vertex sets. Hence each lifted part is one simple cycle of length at least three. Vertex overlaps between different indexed boxes cause no edge conflict because their assigned edge sets are disjoint. An unused twin may be used internally only once in that cycle, exactly as the source explains. No short-cycle algorithm can replace this interface merely by having an edge-injection map.

## 6. Random choices are ordinary checked local trials

The following construction is sufficient; testing expansion is unnecessary.

For folding, draw uniform pairings (with a dummy for odd size), compute the actual loop-plus-collision count Z, and accept only if Z<=2 sum|X|. Source181 gives E Z<=(332/245)sum|X|, so success probability is at least79/245. Delete each loop and all but one edge of every parallel class, preserving the unique representative map and the exact quotient order. Empty active families use the identity. The test, deletions, and sampling are polynomial.

First finish all quotient recursive calls. Then, for a selected original piece R, draw its two edge classes P,T, route the now fixed demands in P, and make one fresh small-residue attempt on R-U with the untouched T. On a failure, redraw the whole local attempt from R. Source edge splitting gives expansion >=D^.90/4 in both classes with probability 1-o(1). Conditional on that event and on the resulting routed graph, fresh reservoir randomness has success probability at least3/4 above a fixed cutoff, by the source's uniform sampling proof and (R). The combined probability is at least1/2. Unselected pieces use the same residue attempt with T=R. All choices are independent of the already fixed quotient decompositions where required.

The residue attempt directly implements the source proof: three edge classes, three disjoint vertex reservoirs, greedy two outside representatives per vertex, path partitions in the three complements, and closure through the appropriate reservoirs. Check degrees/sizes needed by the greedy choices and check the final output contract: assigned-edge partition, <=9r completed parts, <=3 simple residual graphs on disjoint vertex sets, total order <=eta r, and each order <r. Routes also have explicit length, interior, team and edge-disjointness checks. A failed check makes no recursive call. An accepted sample need not be a typical sample; its explicit contracts are all that the deterministic count uses.

In particular, the possible bad-T objection is resolved by retrying the combined P,T/routing/residue attempt, not retrying forever with a fixed bad T. A global restart would not give the required bound and is not part of the comparison. The source batch lemma explicitly makes quotient construction independent of router use and permits arbitrary subsequent quotient partitions, so this ordering uses a paid dependency interface.

Uniform finite sampling uses independent fair bits and rejection from a power-of-two range, with mean less than two trials. A fixed rational reservoir probability can be implemented directly by such sampling; alternatively fix a smaller dyadic probability. Source sampling estimates are uniform for every such fixed positive probability. The finite neighborhood-union witness family in the sampling proof is used only for the probability bound; it is never enumerated by the algorithm.

If X is an attempt cost and p its success probability, the renewal identity is E(total)=E X+(1-p)E(total), conditional on the fixed local data. It does not require X independent of success. Thus every local retry has expected polynomial bit cost and almost-sure termination, without redoing recursive quotient work.

## 7. The actual source induction is stable under these replacements

Here is a common accounting covering both the comparison and the submitted schedule. Let M0=ceil(log2 n), D_j=2^M_j, M_{j+1}=floor(beta M_j), and process stages with M_j>=M_*. If alpha<=beta and M_* is large, choose alpha so that

    alpha M_j <= M_{j+1} <= beta M_j.

If extraction leaves residual degree <=D_j^gamma, require gamma<=alpha. For the comparison take (gamma,alpha,beta)=(.95,.95,.96), K=200. For the author's spectral route take (.98,.98,.99), K=1000. Both satisfy

    1.02 beta^K<.001, gamma beta^K<.001.

Fix P0=4(K+1), eta=1/(100P0), C0=2, C2=2C0/(1-beta), H=C2 alpha^(-K), A1=H+4/3, A2=max(9P0+8,9H). These constants precede M_* and C. The source prefix-selection algorithm is a finite scan of the S_j, valid for either fixed K.

Since M_j<=beta^(j-l)M_l,

    sum_(l<=j)1/M_l <= 1/((1-beta)M_j).

The source product calculation gives n<=N_j<=n(1+C2/M_j)<=2n, also for descendants relative to their ancestor order. Long-cycle cost is at most n/((1-beta)M_j), after imposing D^(-.01)<=1/log2 D. At t=i+K, writing D=D_i,w=M_i,

    N_t<=(1+H/w)n;  long-cycle count<=Hn/w.

Each level-i box Y has y<=D^1.02, descendant order sum between y and (1+H/w)y, descendant orders <=D^.001, and boundary average degree <=D^.001. Thus 2|E(F(Y))|<=2yD^.001. Greedy batches of total descendant order <=D^.30 number at most1+4y/D^.30. At most2yD^(-.009)<=y/w vertices are not good. Skipped small intersections cost at most y(D^(-.87)+4D^(-.15))<=y/w. The original multiplicity argument, choosing one occurrence for each good piece vertex for the lower bound, gives

    S_i-4n/w <= Sigma <= S_i+Hn/w.

Folding and residue processing therefore give, on every accepted execution,

    sum quotient orders <= n-S_i/3+A1 n/w,
    max quotient order <=D^.30,
    sum residual orders <=S_i/100,
    nonrecursive completed parts <=A2(S_i+n/w).        (I)

The exact original edge partition is preserved: long cycles, prefix pieces, and boundary batch edges are disjoint assigned categories. In a batch the four original-edge destinations are trimmed singles, positive-length remnants, folding errors, and retained representatives. Every router edge moves from one piece into exactly one lifted or closed cycle. Residue processing receives only the unused piece edges. No edge is lost or counted twice.

Use the source potential phi(x)=max(1/2,1-1/sqrt(log2 x)), with phi(1)=1/2. Induction and (I) bound the total by

    A2(S_i+n/w)+C S_i/100
       +C phi(D^.30)(n-S_i/3+A1n/w).

For C>=7A2 the S_i coefficient is at most A2-47C/300<=0. Since D<=2n, log2 n>=w-1, and for sufficiently large w,

    phi(n)-phi(D^.30)
      >=[1/sqrt(.30)-sqrt(w/(w-1))]/sqrt(w)
      >=1/(2sqrt(w)).

The remaining overhead is at most C(A1+1)n/w, absorbed by M_*>=4(A1+1)^2. This is the same source potential and the same source savings, with explicit integer-rounding constants.

If no piece occurs, or the selected prefix reaches the last stage, use all stages. Final boundary degree is below D_*=2^M_*, giving fewer than D_*n single edges. In the nonempty terminal case piece order is <=P0 S_i<=2P0n, so completed residue parts cost <=18P0n and residual order <=n/50. The bound T(D_*)n+Cn/4, with T=1/(1-beta)+D_*+18P0 enlarged to an integer, is <=Cn/2 for C>=4T. For every order below the fixed cutoff use original edges singly, enlarging C once. n=0 and all edgeless inputs return the empty list.

Choose fixed exponents and K first, then P0,eta,C2,H,A1,A2, then an absolute integer M_* meeting the finite list of positive-power/logarithm margins and sampling tail bounds, then an absolute integer C. These are computable constants independent of input; there is no nonuniform advice. All scale comparisons are integer power or root comparisons on O(log n)-bit integers. The potential is used in analysis, not evaluated by the algorithm.

## 8. Almost-sure and expected polynomial bit time

Every deterministic subroutine is polynomial in an explicit graph's order: DFS/BFS, components, rational LP and its rounding, path reconstruction, representative maps, and output checks. At each call, N_j<=2n and there are at most ceil(log2 n) stages. Splits have linearly many leaves at each stage, and cycle deletions strictly remove assigned edges. Batches, pieces, and demands are polynomially many. The local retries have uniformly bounded expected repetitions and do not call the main recursive algorithm. Thus the expected local work is <=A(n+1)^a for fixed A,a.

Increase the base cutoff so that every child has order <n/2, w>=A1, and eta<1/2. From (I) the sum of all child orders is <=2n; in terminal cases it is <=n/50. Discard edgeless children without recursion. For every realized child list and every fixed integer p>=4,

    sum_j n_j^p <=(n/2)^(p-1) sum_j n_j
                 <=2^(2-p)n^p <=n^p/4.

This is a pointwise bound, not an average over favorable samples. For p>=a+2, conditional induction on arbitrary realized child graphs and the law of total expectation give expected total cost <=B(n+1)^p after enlarging the absolute integer B for the finite base range. Each child order is smaller, and local trials terminate almost surely; induction gives almost-sure termination of the finite recursive construction. No exponential seed enumeration is used.

Labels are restored through explicit maps using O(log(n+1)) bits per label. Every output has at most |E(G)| edge occurrences, hence O(n² log(n+1)) encoded bits. The deterministic induction gives <=Cn parts on every terminating execution, including accepted samples outside the sufficient expansion events. Thus the integrated comparison covers every computational and output conclusion of frozen S176A.

## 9. Other actual comparisons and resolved objections

BM's Sections 2.5–2.6, 3.3–3.4, 4, and 5 were read, including its hypergraph obstruction, random-vertex proof, sparse skeleton, complementary closure, DFS bypass and iterative degree reduction. BM alone has a log-star total-part bound, so its headline does not subsume S176A. Its weakest robust-expander path theorem is not claimed algorithmized here; the source's stronger cut-expansion regimes allow the CFS specialization. BM Sections 3.1–3.2 and the full transitive ancestry of its sprinkling argument were not read in full and are not algorithmic dependencies of this reduction.

CFS Sections 3 and 5.1 and Lemma 6.3 were read as actual proofs. Its general iterative procedure alone accumulates a log-log factor. Its saturation principle and smaller-side charging are nevertheless compatible with the source's savings, as Sections 4–7 explicitly establish. Using the density theorem with d tending to zero would not retain an absolute linear part bound; that is not the reduction used.

GGKO's full main statements and Proposition 6.3 were read. Its near-optimal decompositions require minimum degree or large-cut assumptions, and Proposition 6.3 imports a universal decomposition for its exceptional subgraph. Thus this does not supply an independent unrestricted algorithm merely by applying a dense theorem. Its regularity/Hamilton-decomposition ancestors were not needed or read in full; I do not infer algorithmic guarantees from them.

AABC v2's maximum-degree-four, even-subgraph exchange, and matching-based 2-regular decomposition proofs were read. The even remainder and matching operations do not turn an arbitrary 2-regular part into one simple cycle. The sum of component-cycle counts can be of order n Delta. The restricted degree-four result and overlapping covers do not supply the frozen unrestricted part bound. Its cover section and all matching ancestry were not read; no cover-to-partition inference is made.

LSY v2's actual contraction algorithm, recursion/size/runtime proof, and PullUp proof were read. Its guarantee is O(n) leftover edges and short cycles. On dense graphs, covering Theta(n²) edges with cycles of length at most a fixed power of log n requires Omega(n²/polylog n) cycle parts. PullUp assumes vertex-disjoint quotient cycles and disjoint clusters; it is not the source's overlapping-cycle routing interface. These are genuine incompatibilities, not grounds for calling the present theorem substantial, since the integrated source/CFS/LR route already pays it.

A late bounded same-family successor query found Kim arXiv:2610.07840v2. I acquired it and read its main statements and complete top-level procedure, not its full heavy-cycle/light-graph proofs. The procedure tests for a heavy cycle and invokes near-closed subgraphs; I do not infer a polynomial implementation or use it in the derivation. Other web snippets, including third-party release/formalization accounts, were incidental navigation and not evidence. No exhaustive current-literature or priority claim is needed for this TECHNICAL conclusion: the explicitly read older mechanisms and stipulated source already give a full-scope construction. Newer alternatives could strengthen that conclusion but are not prerequisites for it.

The original r33/r52 directed target was read at the exact allowed extents and remains distinct and unchanged. The complexity proposal section is only a prior comparison boundary, not proof of this verdict. The r144 session excerpt is administrative navigation, not a mathematical antecedent. No r175 spectral body was needed or read; its supplied unchanged disposition is retained.

The neutral questions have the following contribution-level resolutions. The path primitive is made explicit in Section 2, with its access limitation disclosed. DFS is witness extraction from an existing proof. Spectral loss is affordable but avoidable using LR. The two routing regimes and all-batches load are covered by Section 5. Resampling the whole local piece attempt resolves bad-reservoir conditioning without repeated recursive work. The integer schedule, pointwise count, computable constants and expected bit complexity are covered by Sections 7–8. No nonroutine surviving operation remains after this combination. This does not judge whether every sentence of the submitted correctness proof is valid; that separate role is untouched.

## 10. Limits and handoff

The derivation is mathematical, not an executed graph-decomposition implementation. Artifact checks and rational exponent calculations are not mathematical certification. The complete read/isolation/dependency record is `private/READING-AND-ISOLATION.md`, with exact logged ranges and input bindings. Lovász remains an OCR reading with damaged subscripts, independently reconstructed above, not a recovered local PDF or successful visual reading. LR was acquired and its operative rounding proof read during this review; it was absent from the author's comparison.

**Remaining contribution obligation: none for the scoped TECHNICAL comparison above.** Separate correctness review, any acceptance decision, and every count or integration remain with the parent. No SUBSTANTIAL claim, worldwide novelty claim, downstream artifact, or frozen-scope change is made.
