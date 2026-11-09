# Formalization handback for MathDB 350452

The source proves the literal endpoint `IR350452.conjecture_false : ¬ IR350452.Conjecture` without residual hypotheses. The witness is the explicit 20-edge graph `G9` on `Fin 9`. Its upper irredundance number is 3, its nine maximum irredundant sets are exactly `walk`, and `pathIso` is an explicit isomorphism `SimpleGraph.pathGraph 9 ≃g IRGraph G9`.

The general definitions use closed neighbourhoods and quantify `IsIRGraph` over all finite simple graphs on types in `Type`. `IR` is a finite maximum, with attainment and upper-bound proofs. Source swap adjacency is used directly: symmetry and absence of loops are proved, with no added disequality or symmetrization.

`nonvacuity` proves `IsIRGraph (pathGraph 2)` with source `pathGraph 2`.

This is a formalization handback, not an acceptance or novelty decision. Root retains acceptance authority. The cycle half is not separately refuted.

See `results.json`, the extracted replay logs, `PROOF.md`, and `STATEMENT-CORRESPONDENCE.md`. Development failures are summarized in results.json; final extracted replay logs are retained in full.
