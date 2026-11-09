# MathDB 352827 round 3: partial handback

Status: incomplete; not accepted. The unconditional theorem mathdb_352827 is absent. Root decides.

New modules prove packed-table lookup correspondence at every index and injectivity for both tables, and transport the checked indexed connectivity, distance labelling, and all 116 upper trees to the literal graphs under explicit remaining coverage hypotheses. The new conditional endpoint has exactly three residual Props: Enumeration27, Enumeration28, RotationRepresentativeCoverage28 (src/BridgeTransport.lean). Each enumeration Prop is the exact membership equivalence with the proved-complete reference enumeration. Rotation coverage uses the literal rotateVertex operation.

Still open: efficient gap enumeration completeness and equality with the stored tables, and concrete rotation representative coverage. No cardinality comparison substitutes for equality. Both frozen bridge Props are derived conditionally; neither is asserted unconditionally.

Next round: formalize the inverse that subtracts the rank from each increasing stable subset, prove the gap enumeration complete, and kernel-check its equality with each stored list. Produce per-index representative/rotation witnesses, prove the numerical rotation checker sound using rotateMask_bit, and discharge RotationRepresentativeCoverage28. Apply mathdb_352827_round3_conditional to the resulting three theorems.

All 209 round-2 modules are frozen byte-identically, with before/after hash records. The source archive, fresh replay, full declaration audits and negative controls are recorded in results.json and REPRODUCE.md. Do not interpret PASS_PARTIAL_ONLY as proving the conjecture refutation.

Operational exceptions: initial lightweight shell orchestration was uncapped. One accidental empty /tmp/unused file was created outside the lane by a no-op heredoc; it contained no research data. No other intentional writes outside the lane, git, child agents, network requests, external messages, uploads, browser tabs, shared ledger changes, or self-acceptance. A prohibited rm-style cleanup was automatically rejected; the cleanup was unnecessary. Development failures remain in uniquely named logs.

Fresh validation completed: 362 strict module builds and 362 leanchecker runs passed; the full audit reports 1,329 local declarations. The new negative control initially stopped at maxRecDepth. Only that test's recursion option was raised, then all four negative controls were rerun and rejected their false claims as intended. No mathematical module changed after its fresh build. The initial failure log, initial packet manifest, targeted repair receipt, and final source-identity check are retained; a second full mathematical rebuild was unnecessary because all 362 module source hashes stayed identical.
