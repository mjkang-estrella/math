# MathDB 343536 — grid-formal-r2

PARTIAL CONDITIONAL FORMALIZATION. No acceptance or discovery credit is claimed.
Root decides. The unconditional endpoint has not been obtained.

Completed in new modules:

- Positive-layer propagation, including the missing positivity premise.
- Matching neighbours and cell saturation under neighbour existence.
- Definition 5.1 equivalence with actual neighbour-cell multisets.
- An unconditional complete lattice instance for equitable partitions of every
  finite graph, in source refinement order, with ordinary partition joins.
- Single-unknown-neighbour cancellation and first-row determinism for all grids.
- Equitability under graph isomorphisms and the conjugation-back formulas for
  colour preservation and mapping the chosen vertex.
- The necessary nonexceptionality direction for a full-Aut free vertex.

All 6 round-1 modules, including its auditor, remain byte-identical. New files
are GridPropagation, GridNeighbours, GridLattice, GridDeterminism, GridTransport,
GridFinal2 and Audit2. The pinned original zip hash was verified against
4e63e88b4a18f493fef73f6fcb3de35ef29c78e5612a0ad35e54e7e9a441909c.
The before/after frozen hash manifests record the individual files.

Exact remaining Props are Grid343536.MainOrbit, Grid343536.FreeClassification
and Grid343536.ExceptionalNoIso, unchanged in src/GridFinal.lean.
GridFinal2.mathdb_343536 retains exactly those premises. The general lattice
structure no longer needs an assumption.

Next round: specialize the multiset rule to the saturated border; formalize
non-backtracking walks, corner timing and the explicit A0 map for each side.
Prove generator conjugation identities for WLOG. Construct positive invariant
layers and border transitivity for ordinary grids, paths and ladders, then use
positive_layer_propagation. Finish explicit A0 stabilizers and the exceptional
subgroup collisions. This round certifies no exhaustive finite partition or
subgroup counts; inherited regression tables remain only regression tables.

Validation reports are replay-report.json and verification/replay-report.json.
They distinguish LOCAL and upstream metadata and compare audited inventories
with the full endpoint import closure, including generated declarations.
No new prior-art or significance claim is made by this implementation round.
