# Round 7: closed mask-chain implementation, partial

This packet proves concrete input-mask entailments and supplies named hint dependencies, closing normalized certificate additions [0,5000). All 4,728 input clauses used by that prefix have proved generator entailments and kernel-checked encoding equalities. No local-hint assumptions remain in its named clause theorems. Root decides acceptance; credit is zero.

Endpoint: `Percolation.not_conjecture20_mask_after5000 : Percolation.MaskChain.RemainingSuffixUnsatR7 → ¬ Percolation.Conjecture20`. Its exact remaining semantic obligation is unsatisfiability of the normalized generator together with the proved last clause, mask `(2495223039294576003288924160, 1208935042986666046259200)`. Exactly 124,671 certificate additions, zero-based [5000,129671), have not been replayed by this mask packet. NoMinimalTwoRound5 and the unconditional endpoint remain unproved.

The older 13,561-step list frontier remains separately preserved in inherited.zip, hash 9add6cc761e26a70637ea9a8555199187c705f121a3a25b1159ce2f22ec7637c. It has 116,110 unreplayed suffix additions. These frontiers are alternatives and are never added together.

Fresh strict replay: 303/303 compiler passes and 303/303 explicit-module leanchecker passes. Compiler total 909.00 s; checker total 560.49 s; combined 1469.49 s. These are GNU process wall times, excluding development, failures and shell/watchdog overhead. Peak process RSS: 1871204 KiB. Source scan and local metadata audit, including the expression builder, pass. Printed endpoint axioms are only propext, Classical.choice and Quot.sound.

The full-chain 5,000-step prefix measurement is 1458.67 s for 10,146 hint uses, 6.956 hints/s, including input proofs and fixed dependencies. Its first-1,000 conservative measurement is 1375.10 s for 2,146 hints, 1.561 hints/s; it charges all inputs prepared for 5,000. The windows overlap. These cheap-prefix rates are not heavy-window rates. The required heavy 1,000/5,000 windows [13561,14561) and [13561,18561) remain unmeasured, so no claim that the full packet fits four hours or that one restart strategy is cheaper is justified.

The session hands back a closed implementation prefix rather than a complete certificate. Continue with the heavy full-chain measurements before scaling. The input proofs are a significant cost absent from round 6's approximately 875-hints/s local-check pilot.

Development failures: builder structure syntax and monadic mkArrow corrections; input-proof indentation correction; an out-of-root development test invocation and an invalid checker search-path argument. All logs are retained. No limit was raised. The final packet omits experimental baseline/pilot modules and the historical list replay from its dependencies, while preserving the historical archive unchanged. Every retained original proof/definition/bridge module is byte-identical and hash-compared. No background job remains at handback.

Files: source-only.zip, inherited.zip, module-order.txt, module-times.json, results.json, progress.json, PROOF.md, STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, NEXT.md, fresh-replay.log, fresh-extracted/logs/, retained-source-comparison.json, fresh-source-comparison.json, metadata-audit.txt, axioms.txt, and lane-owned scripts.
