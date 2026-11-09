# 336331 — ordinary proof proposal, source/prior/significance HOLD

No accepted credit. Personally derived by GPT-6.1 Sol, no programs performing mathematics. This is an ordinary proof for independent review, not an independently reviewed result.

## Exact target and source
For every finite connected simple undirected graph G with adjacency matrix A, degree d(v), and x(v)=sqrt(d(v)), if x is an eigenvector of A squared, then G is regular or biregular. Biregular here means bipartite with constant degree on each part; if the two constants coincide the graph is regular. The literal MathDB statement is raw/336331.jsonl. Spiro arXiv:1706.03298v2 (6 September 2017), p.1 defines simple graphs and biregularity; p.2 imposes connectedness; p.11 Conjecture5.9 is the exact target. Lemma5.1, p.10 already proves the conclusion from Ax=cx. The new proposed bridge is A²x=tx implies Ax=cx for this particular x, including bipartite graphs. No claim is made about arbitrary positive vectors: their bipartition squared norms need not agree.

Own saved PDF SHA256 8ca4c89c17a57b965be92193b5e3911062fdc0e60ff7fee809a0f09ffbf3ac2b. Current arXiv abstract gives v2 as latest revision; no journal reference observed there. Live search identified J.Graph Theory90(3),288–303(2019), DOI10.1002/jgt.22401, online24 September2018. First actual final PDF GET returned403; final-body comparison remains unpaid. Author Problems2Solve PDF failed SSL certificate verification; no alternate delivery permitted. Search excerpts are not primary-body evidence.

## Lemma 1: positive eigenvectors of a nonnegative matrix on a connected support component
Let M be a finite symmetric nonnegative matrix. Suppose positive vectors a,b satisfy Ma=t a and Mb=t b, with t>0. On each component of the undirected support relation M_uv>0, b_u/a_u is constant. Proof: choose u maximizing that ratio within the component and write
 t a_u (b_u/a_u) = sum_v M_uv a_v (b_v/a_v),
 t a_u = sum_v M_uv a_v.
Subtract. Every summand M_uv a_v times (maximum minus ratio at v) is nonnegative, and their sum is zero. Thus all support neighbors have the same ratio. Repeat along a finite support path. Apply separately on each component. This proof uses neither numerical eigenvalue computation nor a Perron-Frobenius theorem.

## Lemma 2: components of the two-step support
For a connected graph with at least one edge, the support of A² connects precisely the equivalence classes of even-length walks. If G is bipartite, these are exactly its two parts: vertices within one part have an even path by connectedness, and even walks never leave a part. If G is not bipartite, there is an odd cycle. Any walk between two vertices can be changed in parity by walking from its start to that cycle, once around it, and back; thus an even walk exists between every pair. A walk of length2k yields a support path for A² by grouping consecutive steps in pairs. Conversely each positive A² entry witnesses a length2 walk. Hence there is one support component in the nonbipartite case and two in the bipartite case. Self loops in the support cause no difficulty.

For completeness, the odd-cycle dichotomy has an elementary proof: absent odd closed walks, parity of the length of a path from a chosen root is well-defined; adjacent vertices have opposite parity, giving a bipartition. Any odd closed walk contains an odd cycle by splitting at repetitions until a shortest odd closed walk has no internal repetition.

## The bridge
If G has only one vertex it is0-regular. Otherwise every degree is positive. Set x_v=sqrt(d_v)>0 and y=Ax>0. Assume A²x=t x. The diagonal entry (A²)_vv=d_v>0 shows t>0. Commutation gives A²y=A(A²x)=t y. Apply Lemma1 with M=A² and Lemma2.

If G is nonbipartite, y=cx on its single support component. If G is bipartite with parts U,V, obtain y_U=alpha x_U and y_V=beta x_V. Both constants are positive. Let B be its U-by-V incidence/adjacency block. Then
 alpha sum_{u in U} x_u² = x_U^T B x_V = beta sum_{v in V} x_v².
Both squared norms equal |E(G)|, because each is the degree sum on one side of a bipartition. This number is positive. Consequently alpha=beta, giving y=cx also in this case. This side-volume identity closes the gap that a bare Perron argument for A² would leave.

## Extremal-degree conclusion, independently rederived
Write delta=min d_v and Delta=max d_v. Choose vertices u,v attaining them. From Ax=cx,
 c = (sum_{z~u} sqrt(d_z))/sqrt(delta) <= sqrt(delta Delta)
   <= (sum_{z~v} sqrt(d_z))/sqrt(Delta) = c.
Both inequalities are equalities. Therefore every neighbor of every minimum-degree vertex has degree Delta, and every neighbor of every maximum-degree vertex has degree delta. These conclusions apply to any vertex attaining either extremum, since the same c is fixed. If delta=Delta, G is regular. Otherwise, start at a minimum-degree vertex and follow a path to any other vertex. Degrees alternate delta,Delta along that path. Connectedness therefore puts every vertex in one of these two degree classes; every edge joins opposite classes by the equality conditions. Thus G is biregular. This pays every finite connected simple graph, not just nonbipartite graphs, two-degree quotients, or a finite sample.

## Adversarial self-check and limits
A² need not be irreducible when G is connected: K2 is the smallest warning, so the proof explicitly splits parity classes. Positivity of x and y and t>0 was established before division. Ratio maxima exist by finiteness. The bipartite norm balance is specific to square-root degrees and does not assert the false arbitrary-positive-vector implication. Connectedness is used both in the parity lemma and in propagating extreme degrees. No full-matrix polynomial relation is assumed. The singleton conclusion is dealt with separately, irrespective of whether zero is excluded from the word eigenvector.

No independent review, Lean endpoint, extracted replay, paper acceptance, final journal comparison or exhaustive prior-art audit has happened. The shortness of the bridge is neither a novelty clearance nor a routine-result exclusion. A complete earlier applicable theorem and bridge would be needed to exclude it as known. The exact open-looking label and search no-match do not establish novelty. Keep this candidate parked; no formal dispatch in this lane.
