# Hurlbert formalization lane r1

Completed for root review. This lane does not accept the result or award credit.

* Added the literal all-positive-size conjecture Props `MathDB356266.Conjecture` and `MathDB356266.ConjectureLinear` in Endpoints.lean.
* Proved the required endpoints `conjecture_false : ¬ Conjecture` and `conjectureLinear_false : ¬ ConjectureLinear` by specializing at n = 3, N = 23 and applying the existing explicit full-S4 obstruction.
* Preserved Hurlbert.lean byte for byte, including the six general definitions, the witness, its Euler proof and arbitrary-linear-order nonrealizability proof.
* Added the printed Chung–Diaconis–Graham positive control: `w_cdg`, `t_cdg`, `cdg_euler : EulerOrdering t_cdg` and `cdg_realizes : Realizes t_cdg w_cdg`, both proved by `decide`.
* Documented precisely why injectivity plus coverage forces N+1 = (n+1)! without a separate Lean cardinality theorem, using the explicit bijection to the subtype of permutations. This is the documentation alternative authorized by TASK.txt.
* Packaged proof-source.zip with only the five Lean sources and module-order.txt. A new replay-fresh/ extraction passed one-module-per-process strict builds and explicit-module leanchecker for every module.
* Both endpoint axiom sets are exactly [propext, Classical.choice, Quot.sound]. All 23 namespace declarations passed transitive axiom and metadata audits; all five source files passed the prohibited-token scan.

Artifacts: PROOF.md, STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, results.json, source/output hashes, scripts/ and full logs/. The resumable replay driver accepts an extraction directory and optional starting module. Every heavy call used the required watchdog, affinity and limits. No network, git operations, child agents, external messages, ledger changes or writes to other lanes were performed. No background work remains.

Development logs preserve corrected strict-build failures (a letI style warning and audit elaboration syntax/type errors) before the successful final fresh replay. No resource limit was increased.

The upstream review and root ruling remain the authority for novelty and significance; this lane's formalization adds no independent prior-art clearance. Albert–West's restricted-class example and the unread historical-source limits are acknowledged in STATEMENT-CORRESPONDENCE.md. This supplements the existing discovery packet and is not a manuscript or a new acceptance decision.
