# MathDB 352827 round 5

The unconditional theorem `Schrijver.mathdb_352827 : ¬ SchrijverUnitGap` is proved in `src/EndpointRound5.lean`. There are no remaining enumeration or rotation hypotheses. This is a formalization handback, not self-acceptance; root decides.

Five new mathematical modules close the round-4 gap. PathGenerator proves by strong induction that every finite path-stable set below n is represented by the recursive mask generator at its cardinality. PathCoverage applies this theorem to decoded valid masks and proves exact reference-enumeration equivalence after filtering with validMask. For the inexpensive final computation it also proves coverage after the weaker cyclic endpoint filter. Enumeration27Proof and Enumeration28Proof kernel-decide exact list equalities between that filtered generator and the stored tables, then use the frozen validity proofs for the reverse membership implication. EndpointRound5 applies the frozen round-4 conditional theorem to the two proved enumerations.

All 467 round-4 source modules are byte-identical to the archive with SHA-256 79d7782df41e7e9a52c67b34eaa60ef0fa76b66d6b3e645a8942a70747f83e57. The before/after manifests record their hashes. Only new source modules were added.

Validation artifacts are `results.json`, the fresh extraction's `replay-result.json`, full per-process logs and resource receipts, and the two round-5 declaration audits. The closure audit verifies exact equality with the endpoint import closure; the all-source audit also includes unused frozen source modules. Seven negative controls include incorrect path count and corrupted enumeration alongside five inherited certificate controls. See results.json for actual completed outcomes.

Development failures are retained. The initial full-validMask comparison exceeded Lean's -M3500 memory threshold; the final comparison checks only the cyclic endpoints. An initial audit exposed a compiler-generated partial recursion companion; marking the structurally recursive generator noncomputable removed it while preserving kernel reduction. No forbidden companion is permitted by the final audit.

No child agents, git, shared ledger edits, network access, external messages, uploads or browser tabs were used. All writes are inside this lane. The unread journal-body and bounded novelty limitations in the root ruling remain unchanged. No claim of acceptance or worldwide novelty is made.
