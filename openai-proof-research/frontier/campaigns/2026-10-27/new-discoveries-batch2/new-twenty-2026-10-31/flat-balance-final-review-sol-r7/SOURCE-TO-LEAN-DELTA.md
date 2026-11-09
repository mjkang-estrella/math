# Source-to-Lean delta

| Primary claim | Actual formal objects / reason |
|---|---|
| finite simple undirected graph (introduction p1) | SimpleGraph.Adj, adj_symm, adj_irrefl plus Fintype binder; no conclusion-bearing fields |
| i-cliques are complete vertex subsets | IsClique, cliqueFinset powerset/filter, mem_cliqueFinset, cliqueCount Finset.card; unordered and no proxy |
| global c0=1 (p1) | cliqueFinset_zero, cliqueCount_zero for every G including Fin 0 |
| full finite clique-count sequence | cliqueFinset_empty_of_card_lt, cliqueCount_of_card_lt; every subset has card <= card V |
| unrestricted parity totals (eq14 p6) | odd/even/positive cutoffs for every N>card V; no higher nonzero count omitted; private sum_range_cutoff by induction |
| odd/even global split | oddAddEvenCliqueSum using mod-two dichotomy; evenCliqueSum_decomp separates c0 exactly |
| true absolute difference | subtraction after integer casts in discrepancyNat; natAbs_cast_abs, discrepancyNat_cast_int, natAbs_cast_real, discrepancyNat_cast_real |
| bound at most one | balanced_iff_absInt and balanced_iff_absReal, no Nat truncation |
| flatness (Def2.2 p4) | triangleSet contains unordered 3-cliques incident to both endpoints; Flat bounds each real edge's triangleSet.card by 2; zero triangles allowed |
| witness and counts | K33Adj on Fin3 sum Fin3; K33_clique_card_le excludes >=3; pairFinset injection counts nine unordered pairs; actual c0,c1,c2 =1,6,9 |
| Conjecture2 (p6) | FlatBalancedConjecture universally quantifies V,hV,G; both literal negations are assumption-free |
| revised production route | K33_discrepancy_gt_one -> generic not_balanced_of_one_lt_discrepancy -> existential -> universal negation; original witness-specific not-balanced lemma absent from new closure |
| explicit source real/cutoff universal | r7 audit/R1Link.lean source_bound_iff and source_universal_negation, strict PASS after diagnosed cast annotation fix |

No planarity, no-isolated-edge, connectedness or K4-free restriction imported. No axiom encodes the answer. EmptyGraph controls establish discrepancy 1 and balancedness on zero vertices. The positive-index convention remains a separate discrepancy 3 for the witness. The source inconsistency about D=1 at a root -1 does not invalidate this two-convention refutation.

Generic support/cast/partition theorems are proved translations; they need not all be dependencies of a bounded-count witness proof. The precise endpoint closure is recorded in results/352972-env-audit.json; do not label the entire bridge layer a transitive premise of that endpoint.
