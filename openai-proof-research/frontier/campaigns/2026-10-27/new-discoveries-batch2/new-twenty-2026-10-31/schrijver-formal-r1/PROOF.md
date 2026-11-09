# Proof and formalization status

The ordinary finite certificate computation supports a counterexample at k = 12 and r = 3. This lane has not completed its Lean certificate bridges, so it does not claim an unconditional formal refutation.

The source conjecture would require D(SG(27,12)) - D(SG(28,12)) to belong to {0,1}. It suffices to show that both graphs are connected, the first has a pair at distance at least 8 and every pair in the second has distance at most 6. Their integer diameter difference is then at least 2. The final arithmetic implication and its Mathlib diameter bridges are proved in Definitions.lean, conditional on the two explicitly named residual propositions.

The independently generated distance-8 pair, in the source's one-based notation, is

A = {1,3,5,7,9,11,14,16,18,20,23,25},
B = {1,3,5,7,10,12,15,17,19,21,23,26}.

Their masks are 21669205 and 39144021. Bit i-1 encodes source element i. The source and target indices, full distance labelling and parent trees are in outputs/certificate-27.json.

The own generator removes mandatory gaps: for each ordinary increasing combination c_0 < ... < c_(k-1) from {0,...,n-k}, take positions c_i+i and discard simultaneous endpoints 0,n-1. This parametrizes all increasing stable subsets of the path, and discarding simultaneous endpoints imposes cyclic stability. The corresponding mathematical inverse subtracts i from the i-th selected position. This elementary bijection has not yet been proved in Lean.

All edges are generated directly by distinctness and bitmask disjointness. BFS from one representative of every rotation orbit produces 31 trees for n=27 and 116 for n=28. Rotation preserves cardinality, cyclic nonconsecutiveness and empty intersection, so it is a graph automorphism. This observation is used in the ordinary computation but has not yet been formalized here.

For each tree, all vertices are reached. Every nonroot vertex has a disjoint parent of depth one less. Thus the parents give walks of the labelled lengths and establish connectivity. For the lower labelling at A, each oriented edge u,v satisfies d(v) ≤ d(u)+1, while d(A)=0 and d(B)=8. Induction on a walk forces any A-to-B walk to have length at least 8. Both these general soundness arguments are proved in Checkers.lean. The n=28 tree depths are at most 6; rotating the source of each tree covers every ordered pair, proving the ordinary upper bound 6. The computations also give exact diameters 8 and 6, but exactness is unnecessary for the conjecture refutation.

The own program checks every vertex label from every representative in the independent review certificates after aligning enumeration and rotation. It imports or executes none of the review programs. Results are in outputs/computation.json. A successful Python computation remains evidence, not a Lean proof of the missing bridges.

Minimality context: k=12 is the smallest k found in the retained r≥3 violation search, not proved globally minimal. The earlier expanded-corpus search covered k=2..10, r=1..min(6,k-1), retaining only graphs with at most 6,000 vertices. The review's finite table checks covered k=2..6 including the first diameter-2 tail graph, k=7 n=15..24; n=25 timed out and n=26 exceeded its cap. Its additional k=8..16 search used n=2k+1..2k+5 with a 4,500-vertex cap. Completed instances are preserved in outputs/review-search-coverage.json; JSON records from every retained graphs log, including skips, are in outputs/review-search-events.json. Timeout limitations are as stated above; those are not successful coverage. This lane recomputes only (27,12) and (28,12). No result for skipped parameters or a universal minimality statement is asserted. The n≥4k-2 diameter-2 tail argument in the review is not new finite computational coverage.

Theorem 6 and the r=2 correction route play no role in the conditional endpoint. The published DAM 350 (2024) body is unread; the root ruling retains that limitation. No new novelty clearance or acceptance is asserted here.
