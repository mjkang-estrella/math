# Round 8 implementation report

Endpoint: `Percolation.not_conjecture20_mask_after106061 : Percolation.MaskChain.RemainingSuffixUnsatR8 → ¬ Percolation.Conjecture20`.

Conditional on exactly RemainingSuffixUnsatR8: no valuation satisfies normalizedCNF5 together with the final proved clause, mask (5754986057962046098875290843988827640455757824, 2787593149816327892691964784081045188247552). The actual unreplayed suffix is zero-based additions [106061,129671), 23610 additions.

Closed mask additions: [0,106061). Preserved all 303 round 7 Lean modules byte-identically, verified against the pinned archive. New input proofs are in additional modules. Heavy split boundaries are exactly 13561, 14561 and 18561. The historical list frontier in inherited.zip is preserved separately and is never added to the mask frontier.

Measured full named-dependency heavy windows, charging new input proofs and both checks: [13561,14561): 427.886 hint uses/s (46.98 s compile + 29.94 s check, peak RSS 1837672 KiB); [13561,18561): 456.214 hint uses/s (217.22 s compile + 141.73 s check, peak RSS 1939556 KiB). These overlapping windows are not added together. Named-chain-only and cumulative prefix times are separately reported in results.json. Measurements were recorded before generating the later suffix. Both incremental heavy-window rates exceeded 300 hints/s.

Replay: 781/781 module compiler passes and explicit-module checker passes; compiler 3048.51 s, checker 1832.49 s, combined 4881.00 s; peak RSS 3626408 KiB. Times are successful GNU process wall times, excluding watchdog/driver overhead and development failures. See results.json for the exact replay-tree construction.

Local metadata audit includes every delivered proof module and the expression builder. Source scan passes. Printed endpoint axioms are only propext, Classical.choice and Quot.sound. No acceptance claim; credit remains zero and root decides.

Development incidents: brief overlapping replay chunks were stopped, affected stamps invalidated and modules replayed; exclusive locking added. Expanded input proof indentation was corrected after one module failed. Full records are in incident.txt and logs/development. No limit was raised.

Files: source-only.zip, module-order.txt, module-times.json, results.json, progress.json, PROOF.md, STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, NEXT.md, source-scan.json, retained-source-comparison.json, fresh-source-comparison.json, axioms.txt, metadata-audit.txt, full-logs.zip and lane-owned generators.
