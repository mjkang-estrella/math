# Declaration, proof and obligation audit

All explicit source declarations are inventoried below by textual line reading. This is not a Lean environment enumeration: structure projections/recursors, equation compiler output, tactics' generated auxiliaries and anonymous control example names are not completely exposed by these copies. No explicit private declarations are present. Full generated/private/transitive certification is unpaid R2.

| Line | Kind | Name |
| --- | --- | --- |
| 46 | structure | `SimpleGraph` |
| 63 | def | `IsClique` |
| 69 | def | `cliqueFinset` |
| 74 | def | `cliqueCount` |
| 78 | theorem | `mem_cliqueFinset` |
| 85 | def | `IsTriangle` |
| 90 | def | `triangleSet` |
| 95 | def | `commonNbrFinset` |
| 101 | def | `Flat` |
| 105 | def | `oddCliqueSum` |
| 110 | def | `evenCliqueSum` |
| 114 | def | `evenCliqueSumPos` |
| 121 | def | `discrepancyNat` |
| 125 | def | `discrepancyNatPos` |
| 129 | def | `Balanced` |
| 136 | def | `K33Adj` |
| 143 | def | `K33` |
| 157 | theorem | `K33_adj_il_ir` |
| 160 | theorem | `K33_adj_ir_il` |
| 163 | theorem | `K33_not_adj_ll` |
| 166 | theorem | `K33_not_adj_rr` |
| 169 | theorem | `K33_adj_opposite` |
| 179 | theorem | `K33_adj_ne` |
| 185 | theorem | `K33_symm` |
| 193 | theorem | `card_V6` |
| 197 | theorem | `inl_ne_inr` |
| 202 | theorem | `insert_pair_comm` |
| 217 | def | `pairFinset` |
| 222 | theorem | `K33_clique_card_le` |
| 256 | theorem | `mem_triangleSet` |
| 269 | theorem | `K33_triangleSet_empty` |
| 283 | theorem | `K33_flat` |
| 289 | theorem | `cliqueCount_K33_zero` |
| 304 | theorem | `K33_clique_singleton` |
| 311 | theorem | `cliqueCount_K33_one` |
| 329 | theorem | `K33_clique_pair` |
| 340 | theorem | `cliqueFinset_K33_two` |
| 370 | theorem | `cliqueCount_K33_two` |
| 395 | theorem | `cliqueFinset_K33_ge3` |
| 407 | theorem | `cliqueCount_K33_ge3` |
| 411 | theorem | `cliqueCount_K33_three` |
| 413 | theorem | `cliqueCount_K33_four` |
| 415 | theorem | `cliqueCount_K33_five` |
| 417 | theorem | `cliqueCount_K33_six` |
| 424 | theorem | `oddCliqueSum_K33` |
| 430 | theorem | `evenCliqueSum_K33` |
| 437 | theorem | `evenCliqueSumPos_K33` |
| 448 | theorem | `discrepancyNat_K33` |
| 455 | theorem | `discrepancyNatPos_K33` |
| 460 | theorem | `K33_discrepancy_gt_one` |
| 464 | theorem | `K33_discrepancyPos_gt_one` |
| 469 | theorem | `K33_not_balanced` |
| 484 | def | `FlatBalancedConjecture` |
| 490 | theorem | `flat_not_balanced_exists` |
| 497 | theorem | `not_flat_balanced_conjecture` |

Coverage of every inventory group:

- 46–130: primitive graph laws only, actual clique subsets and triangle incidence. commonNbrFinset is an ordinary adjacency filter, unused by endpoint. Classical noncomputable finset definitions carry no hidden graph condition. The only typeclass parameter is Fintype; no unsafe instance or endpoint-bearing hypothesis is declared. Missing generic equivalence obligations are R1, not hidden in a proof.
- 136–186: K33Adj case split; K33 graph-law proofs eliminate same-side impossible cases or return True. Adjacency lemmas are unfolding facts; opposite-side classification is exhaustive. Distinctness follows from irreflexivity, symmetry from the field. No false same-side branch is used after the recorded repair.
- 193–218: card_V6 is card_sum/card_fin, inl_ne_inr constructor disjointness, insert_pair_comm extensional membership, pairFinset genuine subset constructor. No division or oriented-count surrogate.
- 222–253: card>2 gives three distinct members by erase/card arithmetic. Eight summand cases each select a same-side nonadjacent pair. Erase inequalities pay all distinctness and membership assumptions. No stronger lower-order/nonempty hypothesis is smuggled in; empty/small cliques are handled by the implication assumption.
- 256–286: triangle-set membership is explicit filter membership and subset_univ. A 3-clique contradicts card<=2; triangles empty for all a,b, so flatness follows for actual edges. Ignoring adjacency in the final step is valid because the stronger all-pairs empty statement has already been proved.
- 289–326: empty finset unique and vacuous clique; singleton clique distinctness contradiction; card_eq_one plus singleton injectivity gives exactly six. Generic c0=1 is still absent; witness theorem is unconditional.
- 329–392: clique pair handles four endpoint membership cases. card_eq_two plus opposite-side classification covers both orientations; insert_pair_comm identifies them. Cross-pair injection recovers left and right coordinates using disjoint constructors. card_prod/card_fin gives nine; distinct left/right endpoints pay pair cardinality two.
- 395–417: any k>=3 contradicts card<=2; thus empty clique finset and count zero for every such k. Named 3,4,5,6 specializations are proved, not hypotheses or exhaustive search results.
- 424–441: range 0..6, exact parity and known counts. No discarded unknown nonzero higher term for K33.
- 448–473: two closed decide proofs after rewrite, followed by omega inequalities and real definition unfolding via definitional equality of Balanced. No external oracle, native_decide or truncated natural subtraction.
- 484–500: only Flat -> Balanced over all V/hV/G, explicit existential witness, then ordinary specialization/contradiction. No endpoint parameter can supply its conclusion. Not fixed-graph universality. No new axiom is declared.

Audit352972.lean has only imports and print commands, not proofs closing extra obligations. Its selected axiom list covers 21 queried declarations (including definitions/graph structure), and prints SimpleGraph plus 12 definitions. It omits many explicit theorem bodies and generated declarations. Selected closures show only propext/Classical.choice/Quot.sound in the supplied log; this is useful but narrower than its 'body origin, safety' heading suggests.

Controls352972.lean has ten anonymous positive examples: six vertices; an actual cross edge; count !=8; count !=0; positive discrepancy !=4; positive discrepancy !=0; discrepancies unequal; failed pointwise implication expressed as a proved negation; contrapositive from not balanced; and flatness. Supplied final log records their successful compilation, not failed-test controls or reviewer execution. None alone validates arbitrary-graph source bridges or generic Flat nonvacuity. There is no requirement to alter the faithful Flat definition.

Forbidden mechanisms: none in the visible executable source (no sorry/admit/new axiom/unsafe/partial/native_decide/extern/implementedBy/oracle). Comments mentioning prohibitions are not executable declarations. Trust pinned upstream library truth rather than auditing its foundations. The complete new compiled declaration graph still requires independent audit; do not infer it from textual absence.

Independent Pi audit/replay handoff obligations (not dispatched here): enumerate new declarations and origins including all structure/equation/tactic-generated and private names; inspect types/bodies/safety attributes and implicit universe/instance parameters; inspect transitive references and allowed axiom closures; check new generic bridges and source map; clarify controls as positive proofs; retain failed historical diagnostics; build from source into a demonstrably empty directory with only pinned upstream paths, run strict build/checker and deep audit with contemporary receipts; record original and extracted source hashes, all completed receipt JSONs, tool pins and final immutable verification. Independent execution plus manuscript and root adjudication remain separate gates.
