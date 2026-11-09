# Complete proof and supporting certificate

# The complete impossibility proof

Theorem. G = 2(3P₂ ∨ O₂) has no local antimagic labelling with at most three weights.

Palette reduction. Suppose such a labelling exists. A matching edge and either null vertex form a triangle, so exactly three distinct weights occur. In a component the endpoints of any matching edge have different weights. Both null vertices are adjacent to both endpoints, so both must have the third weight. Every matching pair therefore uses the other two weights, in either orientation. This argument allows color roles to change between components.

Let M_c be the sum of the three matching-edge labels in component c. If its null weight is X and its endpoint weights are Y,Z, its join-edge sum is 2X: each join edge is counted exactly once at the null vertices. Summing the six endpoint weights counts matching labels twice and join labels once. Hence

3(Y + Z) = 2M_c + 2X.                 (1)

The labels are exactly the integers from 1 to 30, and their total is

T = 1 + ⋯ + 30 = 30 · 31 / 2 = 465.                 (2)

Case 1: equal null weights. If both components have null weight X, let Y,Z be the other global weights. Equation (1) gives 2M₀ = 2M₁ = 3(Y+Z) − 2X, so M₀ = M₁. Their join sums total 4X. Thus T = 4X + M₀ + M₁ = 4X + 2M₀ is even, contrary to (2).

Case 2: different null weights. Call them X,Y and call the remaining global weight Z. The endpoint weights are Y,Z in the first component and X,Z in the second. Put S = X+Y and M = M₀+M₁. Adding (1) in both components and using (2) yields

2M = S + 6Z,       465 = 2S + M,       5M = 465 + 12Z.       (3)

There are six matching labels, each at most 30. Thus M ≤ 180 (a deliberately loose bound). From (3),

12Z = 5M − 465 ≤ 5 · 180 − 465 = 435.                 (4)

Each of the six matching pairs has exactly one endpoint of weight Z. These six vertices are independent: the only edges between matching endpoints are within pairs of unequal weights. Their incident edges are all six matching edges, once each, and twelve distinct join edges, two per selected endpoint. No join edge can occur twice because it has just one matching endpoint. Let Q be the sum of these twelve labels. Injectivity and positivity give Q ≥ 1+⋯+12 = 78. Summing weights at the selected endpoints gives 6Z = M+Q. Eliminating M with (3),

5Q = 30Z − 5M = 18Z − 465,     18Z ≥ 5 · 78 + 465 = 855.    (5)

Equations (4) and (5) imply 36Z ≤ 1305 and 36Z ≥ 1710, respectively, which is impossible. Both cases are exhausted, so no such labelling exists. □

# A supporting four-weight certificate and related work

Exact value in ordinary mathematics. In the notation of the explicit graph, each row below supplies the five labels for one matching pair and its four incident join edges. The component and pair indices agree with the definitions above.

| c | j | u v | u x₀ | u x₁ | v x₀ | v x₁ |
| 0 | 0 | 19 | 15 | 11 | 27 | 3 |
| 0 | 1 | 22 | 2 | 21 | 10 | 17 |
| 0 | 2 | 16 | 4 | 25 | 26 | 7 |
| 1 | 0 | 14 | 18 | 13 | 30 | 5 |
| 1 | 1 | 20 | 24 | 1 | 6 | 23 |
| 1 | 2 | 8 | 9 | 28 | 12 | 29 |

The thirty entries are a permutation of {1,…,30}. Every u vertex has weight 45, every v vertex has weight 49, both null vertices in component 0 have weight 84, and both in component 1 have weight 99. For example, the first pair gives 19+15+11 = 45 and 19+27+3 = 49. The first component null sums are (15+27)+(2+10)+(4+26) = 84 and (11+3)+(21+17)+(25+7) = 84. In the second they are (18+30)+(24+6)+(9+12) = 99 and (13+5)+(1+23)+(28+29) = 99.

Every edge is a u-v edge or an endpoint-null edge, so its weights differ. The palette is exactly {45,49,84,99}. Thus χla(G) ≤ 4; the theorem gives χla(G) ≥ 4, establishing equality. The fresh verification script reconstructs the graph, checks all incidence sums and all edges, and compares its output with the independent review certificate. This upper bound is supporting mathematics and is not in the Lean theorem.

Older analogue. Tsz Lung Chan, Gee-Choon Lau and Wai Chee Shiu [2, Theorem 9] prove χla(C₃ + C₃) = 4. Its degree-two setting supplies a relevant older counting/parity analogue. We credit that precedent for the equal-null idea. It does not settle this join graph, whose null vertices have degree six. The new content relative to that analogue is completing the exchanged-null-role case using the six common-weight endpoints and twelve distinct join labels. No monotonicity of χla under taking subgraphs is used or asserted.

Bounded comparison. The independent review reads the source, the disconnected-graph paper [2], a companion join paper, and related tripartite constructions. None of the checked theorem bodies supplies this lower bound. The later formalization lane read the full publisher volume reprint of “Local Antimagic Chromatic Number for Copies of Graphs” [3], overcoming the review’s earlier blocked article-page access. Its constructions and general union upper bounds do not imply this lower bound; our graph is neither regular nor a forest. See the archived SIDE-CHECK.md for the theorem-by-theorem scope comparison.

These are bounded screens, not exhaustive prior-art clearance. OpenAlex citing coverage is incomplete and inconsistent between scalar and query results. The cached current-registry checks are path/topic screens, not full proof-body audits. No priority claim follows from a missing hit. The root ruling assesses significance as a qualified pass, modest: a short refutation of a published universal conjecture. It treats this as distinct from the earlier full t-ary-tree result, despite the shared invariant.
