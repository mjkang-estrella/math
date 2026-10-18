# Technical ordered team-routing lemma

This is a directed adaptation of pinned family181, `sections/routing.tex`, `lem:routing`, including its full union-growth and halving proof. It is explicitly classified as a technical operation, not a substantial nomination.

Let P be a loopless digraph on r≥2 vertices with at most one arc per ordered pair; antiparallel arcs are allowed. Suppose each of the outgoing and incoming boundaries of every U has at least h min(|U|,r−|U|) arcs, where h>0. All logarithms below have base two. Put

g=ceil(8(r/h)log(2r)),  ℓ=2g(1+ceil(log r)).

There is a finite indexed collection of ordered demands x_p→y_p, x_p≠y_p. Each vertex occurs at either end of at most k demands in total, k≥1. Demands are partitioned into teams of size at most b, b≥1; demand p has a forbidden set Z_p of size at most z. If

h≥128[ℓ²(k+b)+z],

there exist directed simple x_p→y_p paths of length at most ℓ, pairwise arc-disjoint, internally avoiding Z_p, with pairwise disjoint internal vertex sets within each team. Endpoint membership in Z_p is permitted. Opposite directed arcs are different resources.

**Proof.** The empty demand family is immediate. For each demand form a hypergraph whose edges are the resources used by candidate directed simple paths: their arcs and one token (v,c) for each internal vertex v and the demand's team c. Every hyperedge has at most 2ℓ resources and is nonempty. Use the stipulated Aharoni–Haxell theorem in source `preliminaries.tex`, `thm:aharoni-haxell`.

If its sufficient matching condition fails on a nonempty set I of demands, choose a maximum matching M in their union. Then |M|≤2ℓ(|I|−1). Let F be the arc resources it uses, and Y_c the vertices whose team-c tokens it uses. We have

|F|≤2ℓ²|I|,  ∑c|Y_c|≤2ℓ²|I|.

Since each team contains at most b demands, at least |I|/2 demands have |Y_c|≤4bℓ². Choose a maximal set I₂ of these demands with mutually disjoint unordered endpoint pairs. Each selected pair meets at most 2k original demands, so |I₂|≥|I|/(4k). Also 2|I|≤kr.

For p∈I₂ delete F and W_p=(Z_p∪Y_c)\{x_p,y_p}, retaining its two endpoints. We have |W_p|≤z+4bℓ²≤h/4. Let T=ℓ/2. The forward radius-T ball from x_p and the backward radius-T ball from y_p cannot both have more than r/2 vertices: otherwise their intersection yields a directed walk x_p→y_p of length≤ℓ, and deleting closed segments yields a directed simple candidate avoiding all matching resources, contradicting maximality of M.

Choose one small ball for each p. At least half the choices have the same direction, forward or backward. Retain only these roots S. They are distinct because the endpoint pairs were disjoint, and

|S|≥|I|/(8k).

Every root retains its individual forbidden set and its common direction. Its radius-T ball in its individual deleted graph has size≤r/2.

For A⊆S nonempty let B_t(A) be the union of its radius-t balls in the individual deleted graphs, in this one common direction. If 0<|B_t(A)|≤r/2 and |F|≤h|B_t(A)|/4, then

|B_{t+1}(A)|≥(1+h/(2r))|B_t(A)|.

Indeed, assign each reached v one root whose path reaches it. In the forward case, the outgoing cut of B has at least h|B| arcs. At most |F| are in F, and at most |W_p|≤h/4 arcs at each v point into its assigned root's forbidden set, since ordered arcs are simple. All remaining cut arcs extend their assigned paths. Each new vertex is the head of at most r arcs, yielding at least h|B|/(2r) new vertices. In the backward case use the incoming cut, reverse the path direction, and count tails instead. The same bound holds because all retained roots have the same direction. Mixing forward and backward roots in this argument would be invalid; the preceding factor-two selection is essential.

Thus any union initially satisfying the deletion threshold grows beyond r/2 after g further steps. If it did not, the growth inequality would apply at every step; singleton cuts give h≤r−1, and log₂(1+h/(2r))≥h/(4r), so the size would grow by a factor at least 2^{gh/(4r)}≥(2r)², a contradiction.

Initially |F|≤2ℓ²|I|≤16kℓ²|S|≤h|S|/4, so B_g(S) has more than r/2 vertices. If a current root set A has a radius-t union larger than r/2 and |A|≥2, split A into two halves. One half A′, of size≤ceil(|A|/2), has its radius-t union larger than r/4. The global resource bound gives

|F|≤2ℓ²|I|≤ℓ²kr≤hr/128<h|B_t(A′)|/4.

Another block of g steps therefore makes that half's union larger than r/2. Repeat. After at most ceil(log|S|) halvings one root remains, with a ball larger than r/2 at radius at most g(1+ceil(log r))=T. This contradicts the small-ball choice.

No nonempty I can fail the hypergraph matching condition. Aharoni–Haxell supplies disjoint representatives, which are precisely the required directed paths with their arc and team-token constraints. ∎

The factor128 is deliberately slack. No optimal constant is claimed. If P is balanced and its arc-counting undirected multigraph has cut expansion H, then each directed cut has half that size, so h=H/2 is available. Arbitrary assigned subgraphs of a balanced P need not be balanced, and arbitrary undirected expansion does not imply this directed hypothesis. This lemma does not create the balanced scale decomposition required by the main research target.
