# Round 8 implementation report

Endpoint: `Percolation.not_conjecture20_unconditional : ¬ Percolation.Conjecture20`.

Unconditional: the empty clause, normalized unsatisfiability and NoMinimalTwoRound5 are proved.

Closed mask additions: [0,129671). Preserved all 303 round 7 Lean modules byte-identically, verified against the pinned archive. New input proofs are in additional modules. Heavy split boundaries are exactly 13561, 14561 and 18561. The historical list frontier in inherited.zip is preserved separately and is never added to the mask frontier.

Measured full named-dependency heavy windows, charging new input proofs and both checks: [13561,14561): 922.450 hint uses/s (21.11 s compile + 14.57 s check, peak RSS 1809804 KiB); [13561,18561): 897.944 hint uses/s (106.55 s compile + 75.82 s check, peak RSS 1861928 KiB). These overlapping windows are not added together. Named-chain-only and cumulative prefix times are separately reported in results.json. Measurements were recorded before generating the later suffix. Both incremental heavy-window rates exceeded 300 hints/s.

Replay: 830/830 module compiler passes and explicit-module checker passes; compiler 2705.27 s, checker 1688.06 s, combined 4393.33 s; peak RSS 2724776 KiB. Times are successful GNU process wall times, excluding watchdog/driver overhead and development failures. See results.json for the exact replay-tree construction.

Local metadata audit includes every delivered proof module and the expression builder. Source scan passes. Printed endpoint axioms are only propext, Classical.choice and Quot.sound. No acceptance claim; credit remains zero and root decides.

Development incidents: brief overlapping replay chunks were stopped, affected stamps invalidated and modules replayed; exclusive locking added. Expanded input proof indentation was corrected after one module failed. Full records are in incident.txt and logs/development. No limit was raised. An earlier unshared-mask version stopped at R8Chain106561 on the fixed -M3500 import-memory limit. MaskChainBuildR8 replaces repeated literal masks with named reducible definitions; the delivered status above describes the subsequent checked version.

Files: source-only.zip, module-order.txt, module-times.json, results.json, progress.json, PROOF.md, STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, NEXT.md, source-scan.json, retained-source-comparison.json, fresh-source-comparison.json, axioms.txt, metadata-audit.txt, full-logs.zip and lane-owned generators.
