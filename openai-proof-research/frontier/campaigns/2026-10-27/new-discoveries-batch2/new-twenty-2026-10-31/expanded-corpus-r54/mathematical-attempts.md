# Mathematical attempts and precise gaps

This is investigator work with zero proposed credit. The source texts, not metadata titles, control each route. All lemmas below are ordinary mathematical observations, not claimed as Lean endpoints or discoveries.

## 360705: source-faithful rainbow irredundance

Primary source: arXiv 2311.06161 PDF, Definition 2 and Conjecture 1. A rainbow committee chooses exactly one vertex of each nonempty color class. A set S is irredundant when every v in S has a closed private neighbor: some w has N[w] intersect S = {v}. This includes w=v when v is isolated in G[S]. The MathDB sentence saying that every color class is a minimal dominating set is not the source definition. No theorem about that surrogate was pursued.

First reduction: irredundance is hereditary. If S is irredundant and T is a subset, the same private neighbor for v in T remains private relative to T. Hence merging two color classes whose union is independent preserves IRC. Given a rainbow committee of the merged coloring, extend it by one vertex from the omitted original class to obtain a committee of the old coloring, then use heredity. Properness uses independence of the merged class. This supplies a legitimate reduction but does not establish that repeated merges reach chi(G): a coloring with a complete class-adjacency quotient can use more than chi(G) colors.

Second reduction: a nonisolated degree-one vertex prevents any IRC coloring. Its neighbor has another color; extend this adjacent pair to a committee. The leaf has no closed private neighbor relative to that pair. Conversely, for a bipartite graph with no degree-one vertices, its two-part coloring is IRC: for an adjacent committee {u,v}, each endpoint has another neighbor outside the pair, which is a private neighbor relative to that pair (bipartiteness prevents adjacency to the other endpoint). Nonadjacent committees are independent. Thus bipartite low-color attempts do not provide a substantive counterexample. Isolated vertices require care; the source Proposition 3 silently assumes nontrivial connected behavior, and no endpoint correction is pursued.

The exact checker enumerates canonical set partitions, checks properness, and directly quantifies over all committees and closed private neighbors. `diagnostics-r2.log` records every labeled graph on 1 through 6 vertices, plus 500 seeded random graphs at each order 7 through 10. No witness was obtained. These are not isomorphism counts. A second search uses planted tripartite graphs containing a triangle, so chi is exactly 3. It tests all proper 3-colorings for IRC and, when none exists, all proper 4-colorings for IRC. The accepted test counts are 181, 154, 183, 195, 205 at orders 8 through 12. No witness was obtained.

Missing mathematical lemma: an arbitrary IRC-colorable graph admits an IRC partition with exactly its ordinary chromatic number, possibly through repartitions that are not merges; alternatively find a finite graph and certify both an IRC coloring and the failure of every chi-coloring. Neither is supplied. A finite witness would have feasible Lean finite semantics, but no witness merits formalization. The actual 2025 publisher body remains unread after HTTP 403. The arXiv body and the publisher abstract are distinct evidence depths. No novelty clearance is claimed.

## 360371: quads, additive energy and affine rank

Primary source: arXiv 2310.09695 Sections 2–5, Conjecture 6; published PDF Conjecture 6.1. Cards are distinct vectors in F2^d. Quads are four-element subsets with XOR zero. Complete sets are affine subspaces. A set S of size l is not contained in a complete set of p=2^ceil(log2 l) cards exactly when its affine rank exceeds ceil(log2 l), assuming ambient dimension at least that value. Translate by a point and use binary Gaussian elimination to test this condition. It is affine rank, not linear rank of the untranslated cards.

Let c_x be the number of unordered distinct pairs of S with XOR x. Then

    q(S) = (1/3) sum_{x != 0} binomial(c_x,2).

Two distinct pairs of the same XOR cannot share a point; their union is a quad. Every quad has exactly three pair partitions. This proves the identity. The ordered additive energy satisfies

    E(S) = l + 6 binomial(l,2) + 24 q(S).

The degenerate ordered solutions have either all four entries equal, or two equal pairs. Thus the conjecture is a rank-sensitive additive-energy extremum problem, not merely an unrestricted energy maximum.

A useful failed construction is S=T union {v}, where T lies in an affine flat and v lies outside its affine span. No quad uses v, since it would express v as a sum of three elements of T. Consequently q(S)=q(T)<=Q(l-1), so this entire one-outlier family cannot refute the conjecture. Larger searches must permit several outside points and cross-coset pair-sum collisions.

All 65,536 subsets of F2^4 were enumerated. The global maxima in this fixed deck, indexed from size 0, are

    0,0,0,0,1,1,3,7,14,14,18,26,39,55,77,105,140.

No outside-minimal-flat subset beats the size-(l-1) maximum in that same deck. This does not prove a global extremal theorem in every dimension. The second search uses dimensions 5 and 6, sizes listed in `sustained-r2.log`, with 15 restarts and 150 single-card replacement proposals per restart. It maintains the affine-rank constraint and compares with the certified-by-direct-count lower bound from {0,...,l-2}. No retained set beats that lower bound. A score above that lower bound alone would not refute the conjecture without an upper bound on Q(l-1).

The first local-search log (`sustained.log`) is SUPERSEDED: the initial random set was not required to satisfy the affine-rank constraint. It produced an invalid apparent violation at dimension 5, l=6. Corrected initialization and independent witness checking remove it. No conclusion uses that first log.

Missing mathematical lemma: for every finite S of affine rank > ceil(log2 |S|), q(S)<=Q(|S|-1) with Q the actual global maximum, or a rigorous global small-size Q bound paired with a violating set. Compression toward an initial segment can decrease affine rank; an ordinary energy-compression inequality does not retain the necessary rank deficit. No such rank-sensitive bridge is proved here. The published conditional extremizer proof still assumes the conjecture; its subsequent theorem cannot be reused unconditionally.

## 360062: source bridge closes route, no new theorem

Source Section 2 defines 2-bootstrap goodness and the connected, at-most-two-block class. Theorem 2.4 proves that diameter 2 and no induced C5 suffice; its two-block argument uses a dominating cut vertex, and its 2-connected maximal-good-subgraph argument rules out outside attachments via induced C5s. Both cases and the proof of Claim 1 were read. A perfect graph has no induced C5: its induced C5 would have chromatic number 3 but clique number 2. Diameter 1 means complete, and any two vertices infect all others. This is an explicit routine bridge for the entire intended claim. The MathDB chordal-like definition does not rescue novelty, since chordal graphs also have no induced C5.

## Other primary-body limits

360353 exactly appears as source Theorem 1.1; only the theorem, introduction and final proof closure, not every case lemma, were inspected. 360354 asks all k, so the same paper's k=2 implication is not a full resolution. 360181 and 360672 have explicit original-refutation attributions in the primary introductions, but the original Hadwin–Larson and Schrijver proof bodies remain unread; their dispositions are old-resolution leads, not independently audited refutations. 360677 is only settled in the admissible setting in the inspected source, which explicitly distinguishes its natural PMod action from the full Schleimer formulation. No scope widening or full exclusion was made. 359840 has full minimum-cover/orthogonality constraints, so arbitrary fractional-cover experiments on cross-intersecting pairs would be unsound. 360219's even-parity vertices only reproduce the conjectured lower bound; the difficult arbitrary-point upper bound remains.
