# Candidate: MathDB 326640

Exact target: Ebadi–Manrique–Jafary–Manora, arXiv:1311.0479v1 (3 November 2013), Definition 4.1 and Conjecture 4.10, PDF pp.6–8. The parameter is the maximum, over all orientations of K_{r,s}, of the minimum cardinality of a vertex set whose **closed out-neighborhood union** has size at least (r+s)/2. It is neither a signed domination function nor ordinary domination. Assume positive integers r≤s and DOM≠1. The answer is 2 for s≤r+2 and ceil((s-r)/2) otherwise.

This resolves the whole stated formula, including all orientations and arbitrary vertex subsets, rather than one orientation or bounded parameter range. No claim of independent acceptance or worldwide priority is made here.

## Ordinary proof

Put h=ceil((r+s)/2). In an orientation, let a be the largest out-degree on the r-side R, and b the largest out-degree on the s-side S. Every cross edge contributes exactly once to the sum of all out-degrees. Therefore

    rs ≤ ra+sb ≤ s(a+b).

Consequently a+b≥r. If r<s and at least one edge points from R to S, then a>0 and ra+sb<s(a+b), so a+b≥r+1. Choose vertices u∈R,v∈S attaining a,b. Their closed out-neighborhood union has exactly a+b+1 vertices: the cross arc between u and v makes exactly one of the two selected vertices already an out-neighbor of the other. Within each side there are no arcs, and the two out-neighborhoods lie on opposite sides.

If s≤r+2, this pair covers at least r+1≥h, proving DOM≤2. Since the graph has positive order, every orientation has minimum at least 1; DOM≠1 forces equality 2.

If s>r+2, put k=ceil((s-r)/2)≥2; h=r+k. If some edge points from R to S, the pair covers at least r+2 vertices. Add at most k−2 uncovered vertices until the covered set has size h. Each added vertex covers itself, so k vertices suffice. If all edges point from S to R, select k vertices in S; they cover all r vertices of R and themselves, again h vertices. Thus DOM≤k.

For the reverse inequality, take the orientation with every edge pointing from S to R. For every selected set T, its closed out-neighborhood is contained in R∪T and hence has size at most r+|T|. To reach h=r+k requires |T|≥k. Thus DOM≥k, completing the formula.

## Lean endpoint and semantic bridges

`packet/Majority.lean` defines R⊕S as the actual vertex type, `arc` as the cross-edge orientation, `cover` as the closed out-neighborhood union over any selected finite subset, `gamma` as the minimum, and `DOM` as the maximum over every Boolean cross-edge matrix. It proves:

- `arc_orientation`: every matrix describes an orientation of the complete bipartite graph.
- `orientation_representation`: every relation with no within-part arcs and exactly one arc per cross pair equals one such matrix orientation. Thus the maximum omits no orientations.
- `majority_criterion`: integer threshold (r+s+1)/2 is equivalent to 2|N⁺[T]|≥r+s.
- `gamma_minimum`: the defined minimum is attained by a set of exactly that cardinality, and bounds every majority out-dominating set below.
- `DOM_maximum`: the defined maximum is attained and bounds every orientation's minimum above.
- `ceiling_spelling`: natural division (s-r+1)/2 has the defining ceiling inequalities.
- `mathdb_326640`: the exact displayed conditional formula on Fin r⊕Fin s, for every positive r≤s satisfying the source's DOM≠1 hypothesis.

No source theorem is imported as a new axiom; even the lower bound is proved directly, rather than assuming Proposition 4.9. No finite checker is used. The proof is structural at all sizes.

## Prior art and significance limits

The source itself proves only the DOM=1 classification (Proposition 4.9), the star case (Proposition 4.6), and other graph families. Those are not new credit. Its original Conjecture 4.10 has exactly the endpoint above. The companion arXiv:1311.0475 concerns signed functions and is not the same parameter. Live primary-source searches for the exact title, upper orientable set majority domination, complete bipartite majority out-domination, and bipartite tournaments did not locate a later resolution. This is a bounded search, not a proof of novelty.

Current Palomar revision 651: exact phrase queries returned no entries; broad `domination` returned distance-shell tomography and a conditional Gromov–Hausdorff result, with different statements. Broad `chromatic` results concern other coloring theorems. Empty entries are not clearance. Current openai/math head is 4eaee87548250b2682affda7d05d947c05554bae (2026-10-30). The full root recursive response is truncated, so a separate **untruncated preprints subtree** was fetched. No relevant title/path was located; theorem bodies across the entire repository were not exhaustively searched. The 1996 orientable-domination paper and the complete 2020 domination handbook were not read in full, so an old general theorem subsuming the new degree argument remains an explicit independent-review question. MathDB returned 403 once and was not retried.

The candidate establishes a sharp infinite-family formula described as difficult by its source. Its new step is elementary, and independent significance review must determine whether this is substantive enough under the campaign standard or a routine consequence of older domination results. The worker does not adjudicate that gate.
