# Exact endpoint status after r2

Zero credit. The mathematical candidate remains held for full Lean semantics and independent novelty review.

Closed in this lane, strict builds and allowed-axiom audits:

1. Actual `SimpleGraph (Fin 19)` G,H from the given edge lists, both connected and acyclic (`treeG`, `treeH`), using explicit root paths and the finite connected-plus-edge-cardinality criterion.
2. Actual adjacency/complement `Matrix.charpoly` equalities over ℚ. Rational P,Q satisfy PQ=QP=I and AP=PB, checked in kernel row by row; `Matrix.charpoly_mul_comm` proves equality. No polynomial output is assumed.
3. Actual intrinsic line-graph charpoly equality: edge-index maps are bijective onto `G.edgeSet`, `H.edgeSet`; `lineIsoG/H` identify the explicitly indexed line graphs with Mathlib `SimpleGraph.lineGraph`. `Iso.reindex_adjMatrix` and `Matrix.charpoly_reindex` transfer the checked equality. The source itself defines cospectrality by equal characteristic polynomials, so no additional eigenvalue-multiset claim is used.
4. Actual canonical RACG: `RACGSemantics330264.matrix` has diagonal1, edge entries2, nonedge entries0 (∞), and `.Group` is Mathlib's `PresentedGroup` quotient, with canonical Coxeter system. The Coxeter relations are exactly involutions and commuting adjacent generators. `generators_commute`, `cancel_commuting_pair`, and `forbidden_pair_not_shortest` prove the shortening direction in that actual group.
5. `GeodesicWords G k` is a subtype of functions `Fin k → V` whose list is shortest (`CoxeterSystem.IsReduced`); `geodesicGrowth` is its actual `Nat.card`. It is not defined by the computed recurrence.
6. The inherited finite clique-state recurrence certificate remains intact in the combined module and proves its discrepancy. It remains disconnected from `geodesicGrowth`.

Still open:

A. Converse normal form: if a word has no two equal letters whose intervening letters are adjacent to that letter, prove it is shortest in the PresentedGroup. This must be proved, not imported as a textual source theorem or a hypothesis. The inspected pinned `Coxeter.Length` proves length bounds, parity, prefix/suffix reducedness and descent ±1, but not exchange/Matsumoto or the graph-product normal form. A bounded search of GroupTheory for graph products/Matsumoto/exchange found only the TODO in Coxeter.Basic. This is a search report, not a proof that no alternative library route exists.

A concrete remaining route is to quotient syntactically reduced words by adjacent commuting swaps, define generator action by deleting a movable occurrence or appending a new letter, prove it is well-defined and involutive, and prove adjacent generator actions commute. The universal property then maps the actual PresentedGroup to permutations of that quotient. Its length changes by at most1 per generator, giving the shortest-word lower bound. The hard unproved step is well-definedness under swaps, including overlap of two movable occurrences. No action, normal form, or faithfulness claim is yet certified here.

B. Prove that clique states record exactly suffix letters movable to the last position and that the fail transition detects exactly the forbidden pair. Combine A with the proved shortening direction.

C. Prove the recurrence counts the cardinality of accepted words of length k. Transfer to the actual `GeodesicWords` subtype and the two numbers at18. The existing list recurrence need not be used if a cleaner Fin-indexed count is proved and related to it.

D. Conclude the exact universal conjecture's negation, audit that endpoint and fresh-extracted strict replay. Current combined replay is explicitly partial.

Prior-art: source-comparison.md closes the specifically unread McKay/Godsil-body task and reads a later numbered-graph-product construction. It neither rejects the candidate merely for old underlying graphs nor certifies novelty. No full public refutation bridge was verified in that bounded comparison. Current MathDB/Palomar state remains inaccessible under inherited403; no retry/bypass.
