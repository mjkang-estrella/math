# Independent ordinary proof for MathDB 343702

All deductions here are personal ordinary mathematics. No mathematical program, finite sweep, numerical experiment, CAS, solver or formal tool was run.

Let S have vertices 0,1,2 and edges {0,1},{1,2}. Define G on {0,1,2}²: distinct pairs are adjacent exactly when one coordinate agrees and the other differs by 1. This defines a finite simple undirected graph on nine vertices. Moving one coordinate and then the other along S connects every pair, so G is connected. Parity of the coordinate sum gives a bipartition. Its minimum degree is 2 and its diameter is 4; neither fact violates any hypothesis of Conjecture 2.9.

For x=(i,j), z=(a,b), every path from x to z uses at least |i-a| first-coordinate moves and at least |j-b| second-coordinate moves. These moves are disjoint types, so its length is at least |i-a|+|j-b|. Moving monotonically in the first coordinate and then monotonically in the second attains this bound. Thus the actual shortest-path distance is

    d((i,j),(a,b)) = |i-a|+|j-b|.

This proves the distance formula rather than replacing graph distance by an unproved metric.

For an ordered horizontal edge u=(k,t), v=(k+1,t), k∈{0,1}, comparison from an arbitrary z=(a,b) cancels |b-t|. For integer a∈{0,1,2}, |a-k|<|a-(k+1)| exactly when a≤k; the reverse inequality holds exactly when a≥k+1. Therefore

    W_uv = {0,...,k} × {0,1,2},
    W_vu = {k+1,...,2} × {0,1,2}.

There are no ties. When k=0 these sides have sizes 3,6; when k=1 they have sizes 6,3. Reversing the ordered edge exchanges the sets. For a vertical ordered edge u=(t,k), v=(t,k+1), cancel |a-t| instead: W_uv={0,1,2}×{0,...,k} and W_vu={0,1,2}×{k+1,...,2}. The same counts apply, and reversing exchanges them. These are all edge types and all orientations. Hence the SINGLE positive rational λ=2>1 works on every edge, with the permitted orientation disjunction. Equivalently each coordinate-center to coordinate-leaf orientation has sides 6 and 3. In particular the definition is met even with the strongest intended global-λ quantifier.

Let c(i,j) be the number of coordinates equal to 1. A coordinate at an endpoint supplies one neighbor, and a coordinate at 1 supplies two. Horizontal and vertical neighbor sets are disjoint. Thus deg(i,j)=2+c(i,j). The three classes c=0,1,2 exhaust all vertices, and are attained at (0,0),(1,0),(1,1). The degree image is exactly {2,3,4}, of cardinality 3.

For t∈{0,1,2}, put f(t)=|t|+|t-1|+|t-2|. Directly from these three terms, f(1)=2 and f(0)=f(2)=3. Summing the proved distance formula over all a,b gives

    D(i,j)=3 f(i)+3 f(j)=18-3 c(i,j).

The same attained classes give the transmission image exactly {18,15,12}, of cardinality 3. The self-distance term is zero, as in the literal source sum. Thus BOTH cardinality assertions of Conjecture 2.9 fail on this one admissible G. This is a full ordinary refutation of the universal statement, not a replacement classification.

Audit extension only, no additional outcome: for K_(1,m), m≥2, let o be its center and L its m leaves. For any leaf ℓ, W_(o,ℓ)={o}∪(L\{ℓ}) has size m and W_(ℓ,o)={ℓ} has size 1. In its d-fold Cartesian power, projection of paths and concatenation of coordinate paths prove additive distance just as above. For an edge changing one coordinate, all other distance terms cancel, so its sides have sizes m(m+1)^(d-1) and (m+1)^(d-1), in either order. A vertex with r leaf coordinates has degree dm-r(m-1). The one-factor transmission is m at o and 2m-1 at a leaf, giving total transmission (m+1)^(d-1)[dm+r(m-1)]. Every r from 0 through d occurs, and m-1>0 makes the d+1 degree and transmission values distinct. This validates the author's symbolic mechanism, but neither earns a second credit nor cures the prior qualification problem.
