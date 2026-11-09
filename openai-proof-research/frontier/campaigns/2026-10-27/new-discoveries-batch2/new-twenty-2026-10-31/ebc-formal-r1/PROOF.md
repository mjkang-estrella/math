# Partial proof and exact remaining work

The endpoint is `EBC337062.conjecture21_false`:

```
DistanceAndCounts → PathSplitting32 → ¬ Conjecture21
```

This is a conditional theorem, not a completed refutation. No credit or acceptance is claimed.

Closed pieces:

1. `shortestPaths` literally filters minimum-length walks by `IsPath`.
   `shortestPaths_eq` removes that filter using Mathlib's checked minimum-length
   walk theorem. Thus `sigma_eq_walk_count` is an unconditional path/walk bridge.
2. Arbitrary-order circulants use Mathlib's loop-free symmetrized `fromRel`;
   `circulant_adj` gives the literal difference/jump adjacency.
3. `Conjecture21` quantifies over all seven classes and all natural n ≥ 1.
   Every order is positive without adding a hypothesis or hidden postulate.
4. The arithmetic uses independently generated BFS tables. For each source,
   the exact splitting-formula sum is checked in Lean, using natural-number
   evaluation and rational normalization. The scaled sums are 2548392 and
   2548896; the actual rational sums are 15169/615 and 15172/615.
5. `betweenness_from_bridges` proves the sum reindexing and transport from the
   two explicit remaining propositions. The values imply non-uniformity and
   negate the conjunction at Class 4, n = 1.
6. `control_uniform` proves unconditional uniformity for C_2(1,1,1), which has
   a genuine edge, and `control_edgeTransitive` proves edge transitivity.
7. `BFSCertificate` checks local distance labels, predecessors and layer-count
   equations, and defines a general arithmetic layer recursion via Nat.rec.

Exactly two premises remain in the endpoint:

* `DistanceAndCounts`: for every x,y : ZMod 32, actual graph distance equals
  `tabDist x.val y.val`, and the literal shortest-path count equals
  `tabCount x.val y.val`. The local BFS equations are checked, but their
  general correctness theorem connecting these data to paths is NOT proved.
* `PathSplitting32`: for every distinct x,y and adjacent u,v in G32,
  sigmaEdge for {u,v} equals the sum of the two orientation products, selected
  by the two distance-additivity tests. Neither this specialized proposition
  nor the requested general path-splitting theorem is proved.

These premises are ordinary Prop arguments. They are not new axioms and are
not asserted to hold by the certificate. The most important missing work is
combinatorial, not arithmetic. No walk objects are enumerated by the kernel.

The source's prior-art question about the 2022 follow-up remains outside this
formalization lane. The review corrects the printed appendix range to 12–15
vertices and rejects speculation about a floating-point explanation.
