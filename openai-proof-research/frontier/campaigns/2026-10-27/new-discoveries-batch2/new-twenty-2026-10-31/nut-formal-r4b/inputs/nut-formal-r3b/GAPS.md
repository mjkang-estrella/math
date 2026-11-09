# Part B incomplete: zero credit

`finite_obstruction : Nut8.FiniteObstruction` is absent. No unconditional endpoint
exists in this lane, and no acceptance is claimed. The unchanged interface has
not been disproved; no interface repair was attempted. Part A belongs to r3a.

1. B1 is proved: arbitrary permutation relabelling preserves Admissible;
   determinant invariance uses mathlib's det_submatrix_equiv_self; principal
   cofactors are permuted by relabel_principal. Arbitrary sign switching
   preserves Structural, determinant, and every principal cofactor. Structural
   is exactly Admissible C (-1) s; admissible_structural discards only the
   epsilon positivity requirement. Refutation transport lemmas are proved.
2. B2 finite closure computations are checked, but universal graph coverage is
   NOT proved. The list sizes are 1, 1, 2, 6, 10, 29, 64, 194. Every eligible
   neighbor mask for every listed source is checked by extensionClosed, with
   an explicit relabelling into the next list. This includes 1,158 extensions
   at order eight and 1,722 across all seven steps. graphIsoCheck_sound and
   extensionClosed_sound are proved. These work with row-major graph bit
   encodings and permutation lists, not mathlib SimpleGraph isomorphisms.
   Still needed: extract the connected subcubic simple support graph from
   Admissible; prove a removable vertex by a spanning-tree leaf; transport the
   deletion to Fin k and the inductive representative; prove its neighborhood
   gives eligibleNeighbors; convert checked permutation lists to actual graph
   equivalences; prove the induction through order eight. Finite closure alone
   does not prove coverage of all connected subcubic graphs.
3. B3 augmentation completeness is absent. There is no Lean enumeration of
   doubled edges and forced diagonal fills and no proof that all Structural
   matrices over each listed support are represented.
4. B4 is partially proved. treeSign gives signs along any explicitly ordered
   rooted tree (strictly decreasing parent indices). treeSign_unit,
   treeSign_edge and treeSign_weight prove sign values and positive normalized
   edge weights. There is no Lean construction of such parent data from a
   connected support graph or conversion back from a BFS relabelling. No
   complete normalized matrix membership theorem exists.
5. B5 checks only the first 32 r2 normalized certificates in the new batch,
   plus the four inherited pilot equalities. These counts can overlap and
   must not be added as distinct coverage. The remaining 9,140 certificate
   records have not been kernel checked here. The generator can emit them,
   but this packet does not include uncompiled assertions for them. The
   32-case trial took 25.92 seconds and 2.44 GB sampled private memory.
   Linear extrapolation suggests roughly two hours for compilation of all
   certificates alone, before separate leanchecker/audit. This is a planning
   estimate, not a resource guarantee. No unsigned pretest is used.
6. B6 composition is absent. Graph completeness, matrix normalization and all
   certificates must feed the transport lemmas to produce finite_obstruction.
   No hypothesis standing in for any missing bridge is asserted as a theorem.

The full assignment is not complete. All delivered Lean declarations are
replayed and audited as a partial packet; a successful partial replay is not a
proof of FiniteObstruction and carries zero solution credit.

Development log limitation: earlier repeated development trials reused log
filenames. Some failed-trial logs were overwritten; see logs/development-history.md.
The final extracted strict replay logs are complete. This is an additional
deviation from the full-log requirement, not an acceptance-ready packet.
