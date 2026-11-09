# Continuation

1. Keep inherited.zip unchanged: it is the complete round 5 source packet, including the 13,561-addition prefix. Do not infer new closed progress from the standalone pilots.
2. Use MaskRUP.check_sound and encode_cnf to connect numeric masks to the generator and previous clauses. Prove concrete mask/list encoding equalities in bounded modules.
3. Extend the direct-expression builder to construct named clause-entailment theorems, passing actual hint theorem references explicitly. Its current `rawSound` declarations have explicit assumptions for every hint mask, so their proofs contain no dependency-database lookup. Do not erase these assumptions without supplying their proofs.
4. Measure 1,000 and 5,000 heavy steps again including input-mask encoding proofs and named dependency assembly. Current results only measure local checks plus conditional soundness. A whole-packet three-hour claim is not yet justified.
5. If the complete chain is fast enough, replay all 129,671 additions, or continue at 13,561 using the inherited prefix. Prove the empty clause and then normalized unsatisfiability, NoMinimalTwoRound5 and the unconditional endpoint.
6. Fresh-extract the complete delivered source packet, strictly compile and explicitly check every module under the same fixed caps, audit all local declarations and print endpoint axioms.

MaskBuild's elaborator performs expression construction only. The proofs passed to Lean.addDecl are ordinary Eq.refl terms for concrete Boolean equations and applications of the proved general soundness theorem. Both the compiler kernel and leanchecker must accept them. No evaluator oracle is used as a proof.
