# T133E: exact-width expander realization for WL equivalence

This author candidate retains scope-freeze.md unchanged. Source truths at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. No independent proof or contribution verdict is claimed.

## 1. Statement and conventions

For a finite graph G of order n>=2 set h(G)=min_{0<|S|<=n/2}|E(S,V\S)|/|S|; put h(G)=infinity for n=1. Let E be the language in the frozen scope: equal-positive-order connected simple undirected uncolored graph pairs of maximum degree<=101 and h>=1/200000, supplied by explicit adjacency matrices, together with binary k>=2, for which joint k-WL equivalence holds. All invalid encodings and violated graph conditions are rejected. Then E is EXPTIME-complete under deterministic polynomial-time many-one reductions, as is its unary-dimension version.

Joint k-WL starts from equality/adjacency types of ordered k-tuples. At each step it retains the old color and the multiset over z of the entire vector of k replacement colors using that same z. Histograms use common color names and are taken separately on the two graphs. The source's Lemma wl-game identifies this equivalence with the K=k+1-slot bijective game: after discards, Duplicator announces a whole bijection before Spoiler selects the next vertex. All marked pairs must preserve equality and adjacency. Winning means surviving every finite play, with no bound on its duration.

## 2. Paid source interfaces

The operative pinned manuscript is Variable-dimension-Weisfeiler-Leman-equivalence-on-general-and-subcubic-graphs-September-25-2026. Its Corollary prop:computation-images compiles any language L in EXPTIME into a product scalar-image instance consistent exactly on L, with address length r=2(p(m)+2)>=8 and a polynomial-size description. Its local affine fibers Z_B^0,Z_B^1 have at most six binary coordinates, with Z_B^1 a nonempty translate of Z_B^0. Projection to each named readout is full.

For consistent instances Proposition prop:exact-projection supplies nonempty families H_U of compatible offset lists on all block sets |U|<=r+1, with exact restriction H_U|_V=H_V. The full game interface Proposition prop:game-reduction says that a graph pair realizes consistency at dimension r if (i) its vertex sets partition into block parts, and each block offset induces a fixed bijection of its whole part, compatible-offset unions being induced-subgraph isomorphisms; (ii) at every history under any winning r+1-slot strategy, marked zero queries decode to legal affine valuations, and simultaneous zero queries at distinct blocks agree on all shared readouts. Decoding must hold even at full slot occupancy.

We use the colored auxiliary graphs Y^epsilon of section06, before its triangle/private-path uncoloring. The source proves that they are simple connected subcubic graphs, partitioned into connected block parts. Sorts distinguish each anchor, each block/channel spine, and each block/channel/tree level. Every sort has at most64 vertices, is nonempty, and its two version cardinalities agree. The source supplies colored block translations: spines indexed by z go to z+xi_B; prefixes go to their translated prefixes; anchors are fixed. These depend only on the one block offset. Compatible unions preserve all edges and nonedges. Between blocks there are only fixed anchor-path edges and equality matchings between opposite-channel roots. Each proper root has exactly one such external neighbor.

The distinguished main vertex s_B^epsilon(z) is the channel-zero spine vertex. For every shared readout rho between distinct blocks B,C, Lemma graph:readout-walk gives a fixed sequence of sorts such that a walk between s_B(z) and s_C(w) following those sorts exists exactly when z|rho=w|rho. The route follows a spine, ascends a prefix tree, crosses the equality matching, descends and returns along a spine. This and the exact-projection/ring-transfer mechanism are paid source operations.

## 3. A common frame and the uncolored graph

Let s be the common number of sorts, with their common source enumeration. Set m=max(2,ceil(sqrt(s))). On V0=Z_m^2 take the four permutations

T0(x,y)=(x+2y,y), T1(x,y)=(x+2y+1,y),
T2(x,y)=(x,y+2x), T3(x,y)=(x,y+2x+1),

with coordinates reduced modulo m. Treat every (v,i) as a separate directed arc v->Ti(v). On forgetting directions the resulting multigraph F has degree8, with loops counted twice. The classical Margulis–Gabber–Galil bound lambda_2<=5 sqrt(2) gives h(F)>2/5. Indeed the spectral-gap Rayleigh estimate for an indicator gives |boundary A|>=(8-5sqrt(2))|A|(1-|A|/m²)>=((8-5sqrt(2))/2)|A| for |A|<=m²/2. In particular F is connected. This is a classical frame, not a newly constructed expander.

Create a station q_v for each v, identical in both graph versions. Assign the s sorts to the first s stations in a fixed lexicographic order; remaining stations are dummy. For every directed arc (v,i) create separate new vertices a_(v,i),b_(v,i) and edges q_v--a_(v,i)--b_(v,i)--q_Ti(v). Keep every original Y^epsilon vertex and edge; join each such vertex to the station of its sort.

Assign target degrees: original Y vertices20; a_(v,i) degree30+2i; b_(v,i) degree31+2i; stations100, except q_(0,0) degree101. Attach to each of these core vertices enough new private leaves to reach its target degree. Every new leaf is attached to just that core vertex. This is possible: a,b initially have degree2; a station has eight arc incidences plus at most64 fiber neighbors, hence degree<=72; an original vertex has degree<=4 after attachment. Even a self-loop arc uses distinct a,b vertices and two distinct edges at its station. Distinct arcs use distinct internal vertices. Therefore the output X^epsilon is simple, undirected and uncolored, of maximum degree101. It is connected because the frame is connected, every source vertex attaches to a station, and all other vertices lie on paths or are leaves.

The frame, including all arc labels, is shared by the two versions. Leaves at stations have the same counts because their sort cardinalities agree. At original vertices, leaf counts depend only on their original degree. Source block translations preserve that degree: internal incidences are preserved; anchor external incidences are fixed; proper roots have precisely one external matching incidence in both versions; no other vertex has an external incidence. Thus any individual offset gives a degree-preserving bijection of its block's original vertices, irrespective of other block offsets. It follows also that the two complete output graphs have equal order.

The full graph is constructed in deterministic polynomial time from the source's finite lists. Its core has O(s+|Y|) vertices, and each core vertex receives at most99 leaves, a fixed bound. Since each sort is nonempty and has at most64 vertices, |Y|<=64s and m²=O(s). There are no exponentially long labels or uncomputed offset witnesses in the compiler.

## 4. Block ownership and announced bijections

Each original Y vertex and its leaves belong to its old block. Each nondummy station and its leaves belong to the block of its sort. Give dummy stations to one fixed block, which exists. Give the a,b vertices and their leaves for an arc to the owner of its tail station. These choices are the same in both versions, partition all vertices, and do not depend on valuations or offsets.

For a block B and offset xi_B, define Psi_(B,xi_B) on its entire part: apply the source colored translation to its original Y vertices; map their leaves in fixed local-index order; fix the labels of all frame-owned vertices and their leaves. Degree preservation above makes the leaf maps bijections. Station attachment is preserved because a translation preserves every sort. All frame edges and their nonedges are preserved because the frame labels are fixed. Within and between translated source parts, the source compatible-union lemma preserves adjacency and nonadjacency. A leaf is adjacent only to its prescribed owner, and all vertex kinds are preserved. Consequently compatible-offset unions are induced-subgraph isomorphisms, including every new kind of vertex.

This verifies the first source game-interface hypothesis. In particular it proves more than responding to a selected vertex. If the active blocks are U with |U|<=r, exact projection extends the old offset list separately to U union {B} for every inactive B. The maps on all parts combine into one bijection before Spoiler selects a vertex. Every frame vertex has a fixed owner too, so any selection activates at most one new block. Incompatible choices for two unselected inactive blocks never need to coexist. Adding arbitrary expander edges between valuation vertices would not have this property: a cross edge could constrain two independent offsets. Here the only new cross-block edges lie in the fixed frame, and all movable vertices attach to fixed stations through their whole invariant sort fibers.

## 5. Recognition at arbitrary winning histories

We verify the second source hypothesis for every winning K=r+1>=9-slot strategy. We repeatedly use the source's reached-history principle: if a property of retained pairs were false, a hypothetical continuation discarding unrelated pairs could force a loss. Thus the property already holds at the original history, without actually performing or reversing that test during a different intended play.

First, paired vertices have equal degrees. Retain one pair and request a second slot. A winning announced bijection must map its entire neighbor set onto the other neighbor set: otherwise Spoiler selects a vertex witnessing disagreement. This also works in the reverse direction by choosing the preimage of a desired second-graph vertex. Hence degree is invariant. Distinct target degrees distinguish original vertices, stations, root, all eight port kinds and leaves. In particular the root is the unique degree101 vertex in each graph, so is always paired with the root.

Next every marked station q_v is paired with the same labelled station q_v. A station response is a station by degree. Keep the station pair and mark the root. Choose any finite path in the connected frame multigraph from the root to v, expressed as a word in the four permutations and their inverses. Follow the corresponding port paths in the expanded graph, keeping the station endpoint plus at most current and next walker pairs; three live slots suffice. From a station there is exactly one neighbor of degree30+2i, the outgoing a_(v,i), and exactly one neighbor of degree31+2i, the incoming b_(Ti^{-1}v,i). From an a vertex its unique b-type neighbor is the b of that arc; from b its unique station neighbor is the arc head. Reverse steps obey the analogous rules. All extra neighbors are leaves or different degree types. Thus the response walk is forced to follow the identical permutation word from the identical root. At its final source endpoint equality with the retained station forces the target endpoint to be q_v. This argument permits arbitrarily many rounds but never more than three live slots; no uniform first-order quantifier-depth bound is asserted.

Every marked original vertex therefore preserves its sort. Mark its unique station neighbor while retaining that vertex. The neighbor is forced to map to a station neighbor, because its degree is100 or101. Its label is fixed by the preceding station invariant. The response original vertex consequently lies in the same station fiber. Each source sort belongs to one block and vertex role. In particular s_B^0(0) is answered by s_B^1(zeta_B) for a unique legal valuation zeta_B.

Finally retain two zero queries at distinct blocks B,C sharing rho. Their source readouts are equal. The paid source readout-walk lemma supplies a finite sort-prescribed walk between these original vertices. Walk along it while retaining both endpoints and at most two consecutive intermediate pairs; four slots suffice. At every reached history sort is invariant, and adjacency between any two original vertices in X is exactly adjacency in Y. Thus the response sequence is a walk with exactly the prescribed sorts between the decoded query vertices. The converse direction of the source readout-walk lemma forces zeta_B|rho=zeta_C|rho. Walk repetitions cause no difficulty: equality of marked vertices is part of every partial isomorphism, and duplicate slots are permitted. The auxiliary sort/station tests are separate hypothetical continuations, so their pebble costs are not added to the four walking slots. These conclusions apply even when all K slots were occupied in the original history.

Take the query sets D_B^epsilon(z)={s_B^epsilon(z)}. They are nonempty and disjoint. Sections4–5 establish both hypotheses of the source realization interface for X^0,X^1. Therefore for every product scalar-image instance with r>=8,

instance consistent iff X^0 is joint-r-WL equivalent to X^1.

This preserves exactly r, rather than multiplying the dimension or consuming spare ring-transfer slots.

## 6. Uniform expansion

Partition each output into station cells C_v. The cell contains q_v and its leaves, all original vertices in its fiber and their leaves, and a_(v,i),b_(v,i) and their leaves for i=0,1,2,3. Each cell is connected via its station. Its size is at most

101 + 64*20 + sum_(i=0)^3((30+2i-1)+(31+2i-1)) =1641 < C=2048.

The bound includes the root station, whose total station-plus-leaf count is at most102 but in fact at most94 because its base degree is at least8; thus101 is safe. An original vertex with at least its station neighbor contributes at most20 vertices including leaves. Each port has base degree2 and contributes target-degree minus1 vertices. All estimates are uniform in the source input.

Between cells, the edges b_(v,i)--q_Ti(v) realize precisely the frame arc multigraph, with all parallel arcs counted separately. Self-arcs remain internal and do not affect a cut. Extra original Y edges can only increase the boundary. Write h0=2/5 and d=8 for a lower bound on frame expansion and its multigraph degree.

Fix a nonempty S of size at most half the output order, and let I,J,M denote respectively cells wholly inside S, wholly outside S, and mixed. Every mixed cell has a cut edge inside its connected induced cell, and these edges are distinct across cells. Thus boundary(S)>=|M|. Also

|S|<=C(|I|+|M|), and |V\S|<=C(|J|+|M|).

If |M|>=h0|S|/(4Cd), this proves the desired bound. Otherwise h0/(4d)<1/2 implies |I|,|J|>=|S|/(2C), using |V\S|>=|S|. Apply frame expansion to I: the number of frame edges from I to J union M is at least h0 min(|I|,|J|+|M|)>=h0|S|/(2C). At most d|M| of them reach M. Therefore at least h0|S|/(4C) frame edges go directly from I to J. Each is an actual distinct output cut edge, so in this case the stronger bound holds. Combining the two cases gives

h(X^epsilon)>=h0/(4Cd)=1/163840>1/200000.

This argument uses bounded connected cells, not equal cell sizes, and holds on both consistent and inconsistent source instances.

## 7. Complexity conclusion

For any fixed L in EXPTIME use the source compiler of section2. Construct its Y^0,Y^1 and common sort enumeration from the finite local block lists, then construct the common frame above and output X^0,X^1,k=r. The source uniformity section proves that the colored intermediate lists and sorts have size O_M((r+2)^8), and that all finite enumeration can be performed in time polynomial in the original input length. Our additional operations use only modular arithmetic on O(log s)-bit integers, fixed-size decorations, and explicit adjacency-matrix output of polynomial size. The graph conditions hold on every input. By section5 and the source polarity,

w belongs to L iff the scalar-image instance is consistent iff (X^0,X^1,r) belongs to E.

This is deterministic polynomial-time many-one hardness. The output dimension r is polynomial in input length, so writing it in unary preserves the reduction.

For membership, check adjacency matrix syntax, simple undirected structure, equal positive order, degree bound and connectivity in polynomial time. Enumerate every subset in each graph, using integer comparison 200000|boundary S|>=|S| for 0<|S|<=n/2; this takes 2^n times a polynomial and rejects exactly violations of the expansion condition. Handle n=1 directly. Compare the binary k with n before allocating tuple tables; for n>=2 replace k by min(k,n), as justified by source Lemma lem:dimension-cap. Then run its explicit common-color refinement algorithm in time 2^{O(n log n)} times a polynomial in input length, accepting precisely equal stable histograms. This is exponential time in the matrix-input bit length even for arbitrarily large binary k. For unary k, convert to binary first. This proves the full frozen theorem.

## 8. Attribution and limits

The computation encoding, finite affine witnesses, exact projection, readout routes, whole-bijection strategy and ring-transfer converse are source133 inputs. The expander and spectral-to-cut estimate are classical. Degree tags, deterministic port walks and bounded-decoration expansion are elementary tools. The proposed additional operation is their synchronized common-frame encoding that preserves source offsets and exact game width while retaining uniform expansion. Classical CFI expander obstructions and color recovery are not claimed as new. Whether this combined operation is substantial rather than routine is explicitly unresolved here. No full formalization, independent proof verdict, global priority claim, or campaign acceptance is asserted.
