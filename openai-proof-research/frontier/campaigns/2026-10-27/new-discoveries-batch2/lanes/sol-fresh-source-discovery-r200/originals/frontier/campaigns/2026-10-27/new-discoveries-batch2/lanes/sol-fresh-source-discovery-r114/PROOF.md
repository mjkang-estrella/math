# A counterexample to Baskoro–Dalfó–Fiol–Simanjuntak Conjecture 4.2

This is a complete ordinary proof of a counterexample, not an exact metric-dimension classification. Discovery eligibility and current priority remain separate HOLDs pending review.

The source is *On some metric properties of supertoken graphs*, Utilitas Mathematica 123 (2025), 19–33, Conjecture 4.2, printed page 28. Its universal assertion is dim(F_k(K_n))=n−1, for the supertoken graph defined in Section 3: nonnegative integral occupancy vectors summing to k, adjacent when one token moves along one base edge. Repetitions are allowed. We disprove this assertion at k=2,n=10. This is a counterexample to the entire universal assertion, not a proof of an arbitrary-parameter replacement formula.

For occupancy vectors x,y of total 2 on K_n,

    d(x,y) = 2 − Σ_i min(x_i,y_i).

Indeed the sum on the right counts tokens that can remain in place. Every excess token must move at least once; because every pair of distinct base vertices is adjacent, moving each excess token directly to a deficit vertex attains this lower bound. This proves the distance formula without assuming a matching algorithm.

Take the following eight actual vertices as landmarks, written as multisets:

    R = {12,23,34,45,67,78,89,9·10}.

Here 12 means one token at 1 and one at 2; 9·10 means one token at each of 9 and 10. The two base blocks are A={1,2,3,4,5} and B={6,7,8,9,10}. These are landmark-support blocks, not disconnected components of the base graph: the base graph remains K_10.

For any x let T={i:x_i>0}. Since every landmark r has two distinct token positions, its overlap with x is |T∩r|. Thus its distance to x is 2−|T∩r|. Recovering the eight overlap counts from the eight distances therefore suffices to recover x.

On a five-position block, the four landmark edges form a path. The incidence columns for its five positions are

    c1=1000, c2=1100, c3=0110, c4=0011, c5=0001.

The possible nonempty supports of size at most two give the five columns and the ten sums of distinct columns:

    {1}:1000  {2}:1100  {3}:0110  {4}:0011  {5}:0001
    {1,2}:2100  {1,3}:1110  {1,4}:1011  {1,5}:1001
    {2,3}:1210  {2,4}:1111  {2,5}:1101
    {3,4}:0121  {3,5}:0111  {4,5}:0012.

All fifteen displayed vectors are distinct and nonzero. This finite table is itself an exhaustive proof: the only possibilities for a subset of size one or two of a five-element block are precisely the displayed five plus ten possibilities. Include 0000 for the empty support, which is different from all fifteen.

Consequently the first four overlap counts determine T∩A, and the last four determine T∩B, since |T|≤2. Together they determine T. Finally T determines x: if T={i}, both tokens are at i; if T={i,j}, one token is at each position. Thus all 55 vertices have distinct distance vectors to R, so R is resolving and

    dim(F_2(K_10)) ≤ 8 < 9 = 10−1.

This contradicts the printed conjecture. No assertion that the dimension equals eight is needed.

## Closest classical comparison and strongest objection

Bailey–Cameron, *Base size, metric dimension and other invariants of groups and graphs* (2011), actual author-manuscript Theorem 3.32 and Corollary 3.33, pp24–25, prove the metric dimension of the Johnson graph J(n,2). Their proof uses landmark edges in disjoint three-position paths and five classes of signatures. That graph contains only distinct-position configurations. It omits the ten doubled vertices in our source graph. A three-position-path landmark block {12,23} fails here: the doubled vertex 22 and the vertex 13 both give overlap vector (1,1); adding disconnected blocks does not distinguish them. Hence the literal classical construction and theorem do not establish this counterexample.

Nevertheless, the new construction uses the same incidence-signature mechanism, replacing three-position paths by five-position paths to separate singleton and pair supports. This is the strongest substantive objection: the repair might be judged a routine classical adaptation under the campaign's strict credit rule. A full ordinary proof does not settle that judgment. No independent substantive PASS is claimed, and no Lean or manuscript work is authorized by this report.

The 2026 Reyes–Dalfó–Fiol successor was also inspected: Section 2 repeats metric upper bounds; the later proofs concern independence, clique number, coloring and spectra. The inspected body does not supply this resolving set. This is a bounded source comparison, not a global absence claim.
