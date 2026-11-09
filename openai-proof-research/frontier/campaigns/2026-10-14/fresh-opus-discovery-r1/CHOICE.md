# Chosen family (collision-avoidance record)

- **Family: 186** — "Uniform influence and sharp thresholds for graph and hypergraph properties."
- Pinned sources (pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`):
  - `preprints/A-Sharp-Threshold-Bound-for-Monotone-Graph-Properties-September-25-2026/` (graph, r=2, exponent 2)
  - `preprints/A-uniform-influence-bound-for-hypergraph-properties-October-5-2026/` (r>=3, exponent r/(r-1))
- Lane: discrete / combinatorial (Boolean Fourier analysis of random graphs/hypergraphs).
- Recorded: 2026-10-18 by fresh-opus-discovery-r1.

## Freshness evidence
- `tasks.json` (orchestrator registry) + full scan of every campaign subdir's top-level
  working files: family 186 not claimed/developed (no `family186`/`source186` token, no
  substantive working file). Only catalogue-title listings and the r39 history-index
  excerpt (an indexing artifact, not development).
- Semantic grep for "Friedgut-Kalai / sharp threshold / uniform influence" across campaign
  working dirs: only catalogue indices, r39 history index, and unrelated families
  (t117q = uniform sparsest cut, accepted R038; r46 permutation screen; r216a review).
- Not in accepted set (R023-R039), not in exclusion list
  (019,031,144,241,267,282,322,338,012,290,292), not a credited antecedent (unlike 170).

## Scope note
Both papers are COMPLETE on the headline front: they prove the Friedgut-Kalai
sharp-threshold conjecture with the optimal exponent for every uniformity r>=2
(r=2 -> (log n)^-2, r>=3 -> (log n)^(-r/(r-1))), uniformly in bias p, and the
underlying variance-influence bound holds for ALL vertex-relabelling-invariant
Boolean f (no monotonicity needed). Therefore "extend threshold to hypergraphs"
is NOT available. The genuine remaining gap is being determined by reading the
full proofs (restriction/fourier/completion) before freezing a target.
