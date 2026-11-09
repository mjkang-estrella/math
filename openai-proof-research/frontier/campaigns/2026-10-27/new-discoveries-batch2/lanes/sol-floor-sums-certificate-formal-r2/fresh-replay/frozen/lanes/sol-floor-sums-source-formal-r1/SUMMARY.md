# Partial formal result — endpoint HOLD

The unconditional four-variable lower bound has NOT been proved in Lean in this lane. Prior, substantive acceptance, and campaign acceptance remain HOLD. Counts stay 9 additional / 39 total / next 40; root alone accepts. No manuscript, shared file, git state, public service, or MathDB was edited. No children were launched.

Four source modules give a checked, unconditional reduction for every positive natural m, indexed a : Fin 4 → Nat with entries < m, and K < m:

- `FloorSums.literal_eq_clamped` in Reduction.lean proves exact equality of the literal signed integer sum and all 64 clamps. `threshold_count` handles arbitrary integer thresholds, including equality boundaries. `quotient_thresholds` proves the four-threshold formula with explicit natural division before casting to Int. `subset_sum_bound` proves the necessary numerator bound.
- `Symmetry.lean` proves `literal_permutation` and `sorted_representative`, with no distinctness assumption.
- `Source.lean` proves `actual_real_floor` and `actual_source_sum`, identifying actual real floors with the natural quotients. `source_arguments` explicitly proves nonnegative arguments and positive real denominator.
- `FloorSums.explicit_sixteen` in Expansion.lean proves the exact signed expansion for any integer-valued function on indexed subsets, including the empty subset. `sixteen_subsets` independently computes the cardinality 16. `prefix_parameters` and `residue_parameters` prove the prefix/residue interfaces.

`LiteralEndpoint` is the literal requested all-parameter proposition. `SortedClampedBound` is the exact remaining central inequality, DEFINED BUT NOT PROVED. `endpoint_of_sorted_clamped_bound` is explicitly conditional on that proposition. It supplies a proved transfer, not an unconditional bound or a trusted source bridge.

No Python or Z3 result appears in a Lean hypothesis or axiom. No certificate rule was elaborated into Lean. In particular none of the 1,329 arithmetic leaves, Boolean normalization, definition extensions, or 12,459-rule DAG has a formal PASS here. The substantial component is the literal source reduction, not checker soundness.

Run `bash run.sh` in this directory with the pinned installations available. It serially builds Reduction, Symmetry, Source, Expansion, then audits every actual owned declaration including generated/private declarations. `audit-receipt.json` and `Audit.log` contain actual declaration types, origins, safety and transitive axioms. Only propext, Classical.choice and Quot.sound are permitted. `source-only.tar.gz` is deterministic and contains no compiled artifacts; `fresh-replay/` records a fresh extracted build. `final-manifest.json` excludes only itself and the final verification receipt. Archive SHA256 is in `archive-receipt.json`; separate final verification is in `final-verification-receipt.json`.
