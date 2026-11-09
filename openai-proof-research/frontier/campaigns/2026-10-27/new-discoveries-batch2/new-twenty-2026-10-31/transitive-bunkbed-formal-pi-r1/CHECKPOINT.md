# CHECKPOINT transitive-bunkbed-formal-pi-r1 (Pi GLM5.3Flash high)

Bootstrap receipt preserved (bootstrap-receipt.json). 245/245 frozen verified before target/math/source reads (frozen-before.json). Review/qualification/author artifacts read.

Plan: src/BunkbedBase.lean (tokens, arc, reach, monotonicity, last-step, recursive characterization, prefix invariance) -> src/BunkbedCount.lean (trichotomy split equivs, marked-fiber counts, state P_k, kernel C, symmetry/no-crossing/transition) -> src/BunkbedFinal.lean (dominance induction, payoff, literal event-cardinality endpoint, case analysis) -> audit + frozen-after + manifest.

Status: lane scaffolding done; no Lean run yet in this lane.

## 2026-11-06 progress
- BunkbedBase.lean compiles EXIT 0 (runner receipt). Literal model + path lemmas done.
