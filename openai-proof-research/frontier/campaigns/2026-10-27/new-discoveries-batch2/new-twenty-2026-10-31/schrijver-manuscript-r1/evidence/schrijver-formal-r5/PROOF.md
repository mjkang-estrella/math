# Proof of the counterexample

The unconditional Lean theorem Schrijver.mathdb_352827 refutes the literal unit-gap conjecture. It specializes to k=12 and r=3: the literal SG(27,12) is connected with a pair at distance 8, and the literal SG(28,12) is connected with every pair at distance at most 6. Thus the integer diameter difference is at least 2 and cannot belong to {0,1}. The frozen metric and certificate theorems establish these conclusions once enumeration completeness is supplied. Round 5 supplies it without residual hypotheses.

The distance-8 pair in one-based source coordinates is

A = {1,3,5,7,9,11,14,16,18,20,23,25},
B = {1,3,5,7,10,12,15,17,19,21,23,26}.

Their masks are 21669205 and 39144021; bit i-1 denotes source element i. The frozen indexed proof uses indices 29 and 143. A 1-Lipschitz labelling on every edge with endpoint labels 0 and 8 proves the distance lower bound by induction on walks. Certified parent trees prove connectivity. For n=28, the 116 representative trees have depth at most 6; proved rotation automorphisms and complete rotation coverage transfer this bound to every pair.

The new enumeration argument uses pathMasks n k. For k=0 its output is [0]. For n=0 and positive k it is empty. For n+1 positions and k+1 selected positions, its output is the concatenation of pathMasks n (k+1) with pathMasks (n-1) k after setting bit n. If a path-stable finite set s below n+1 omits n, use the first branch. If it contains n, remove n. Stability excludes n-1, so the remaining k positions lie below n-1; use the second branch. The exceptional n=0 case is handled by natural subtraction and the empty remainder. The cardinality-erase identity and equality of all test bits prove the reconstruction. PathGenerator formalizes this induction for the encoding of arbitrary Finset Nat, without assuming enumeration counts.

For any valid mask, take the image of decode n m under Fin.val. Injectivity preserves its cardinality k, boundedness gives positions below n, and cyclic stability implies path stability. Test-bit extensionality identifies its encoding with m. Therefore every valid mask occurs in pathMasks n k. PathCoverage proves that filtering these candidates by validMask is exactly equivalent to membership in referenceMasks, in both directions.

For the final inexpensive comparison, retain only candidates without simultaneous bits 0 and n-1. Every valid mask survives: stability applied to n-1 and 0 prohibits the cyclic endpoint pair. Kernel decision proves exact list equalities of this endMasks output with vertexMasks27.toList and vertexMasks28, respectively. Hence every reference mask is in the table. Conversely, every table entry is valid by the frozen validity certificates, hence belongs to referenceMasks. This proves precisely Enumeration27 and Enumeration28. EndpointRound5 applies mathdb_352827_round4_conditional to these theorems. No count or Python computation is used as a logical premise.

Exact diameters 8 and 6 are supported by the original independent computations, but the endpoint uses only the lower and upper bounds stated above. It does not rely on the false source Theorem 6 or an r=2 graph.

Minimality context: k=12 is the smallest k found in the retained r≥3 violation search, not proved globally minimal. The earlier expanded-corpus search covered k=2..10, r=1..min(6,k-1), retaining only graphs with at most 6,000 vertices. The review's finite table checks covered k=2..6 including the first diameter-2 tail graph, k=7 n=15..24; n=25 timed out and n=26 exceeded its cap. Its additional k=8..16 search used n=2k+1..2k+5 with a 4,500-vertex cap. Completed instances are preserved in outputs/review-search-coverage.json; JSON records from every retained graphs log, including skips, are in outputs/review-search-events.json. Timeout limitations are as stated above; those are not successful coverage. This lane recomputes only (27,12) and (28,12). No result for skipped parameters or a universal minimality statement is asserted. The n≥4k-2 diameter-2 tail argument in the review is not new finite computational coverage.

The DAM 350 (2024) journal body remains unread, as disclosed in the root ruling. This implementation does not assert new novelty clearance or acceptance. Root decides.
