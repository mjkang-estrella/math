# Cartesian powers of the three-vertex path
Ordinary full-scope counterexample to Pourhadi–Faghani arXiv1909.02634v1 Conjecture2.9, pending independent review. Root recommends routine classical-adaptation exclusion, not a claim of prior printed refutation. No novelty or credit claimed.

The actual source Definition1.1 and Section2 require, for each edge uv, that the two sets of vertices closer to u and v have cardinalities in a fixed ratio lambda>1, either orientation. Conjecture2.9 asserts exactly two distinct vertex degrees and exactly two distinct transmissions. The frozen primary text was read before this construction; no use of its bipartiteness proof is needed.

For any integer r>=2, take G=P3 Cartesian-power r. Explicitly V={0,1,2}^r; two vertices are adjacent iff they differ by1 in precisely one coordinate. This is a finite simple connected undirected bipartite graph. Its distance is the sum of absolute coordinate differences: every edge changes that sum by at most1, while coordinate-by-coordinate paths attain it.

Consider an edge differing in coordinate j, first between0 and1. Distances to its endpoints differ only in coordinate j. Vertices with coordinate0 are closer to the0 endpoint; those with coordinate1 or2 are closer to the1 endpoint. The two counts are therefore 3^(r-1) and2*3^(r-1). The edge1--2 gives the reversed analogous counts. Every edge has ratio lambda=2. This proves the exact source property globally.

For a vertex x with k endpoint coordinates (0 or2) and r-k central coordinates1, its degree is k+2(r-k)=2r-k. All k=0,...,r occur, giving r+1 distinct degrees.

Its transmission is
D(x)=sum_y sum_j |x_j-y_j|
    =3^(r-1) sum_j sum_{a=0}^2 |x_j-a|
    =3^(r-1)(2r+k).
The last identity uses one-coordinate sums2 at the center and3 at an endpoint. Thus there are r+1 distinct transmissions as well.

For r=2, the nine-vertex grid has degrees {2,3,4}, transmissions {12,15,18}, and distance-set sizes {3,6} on every edge. Both asserted equalities to2 fail. Cartesian powers yield arbitrarily many values; no additional family credit is implied.

Substantive objection: this is the standard additive Cartesian-product metric applied to the elementary known quasi-2 graph P3=K_(1,2). Equal-factor products preserve each edge's distance-set ratio, while degrees and transmissions add. The displayed calculation supplies every step of that classical product bridge; no new structural classification or missing analytic lemma is involved. Root proposes exclusion under the campaign's routine-adaptation rule, pending independent assessment. Literature novelty and live registry coverage have not been cleared. A known generic product formula alone is not asserted to be a prior printed endpoint.

The exact BFS checks are diagnostics; the formulas above prove every r.
