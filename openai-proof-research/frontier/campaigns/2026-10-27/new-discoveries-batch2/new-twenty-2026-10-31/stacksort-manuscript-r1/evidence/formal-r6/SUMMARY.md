# Round 6 implementation — not acceptance

All requested proof obligations are now unconditional in StackSortFinal6.lean, namespace StackSort.Round6:

- taggedDeletionCount_proved and fixedMaximumDecomposition_proved;
- maximumFinalCount_proved and additiveRecursion_proved;
- exactSeeds20_proved and lower130;
- mathdb_345545, limit_ge, nonvacuity and subsequence_companion;
- mathdb_345545_max and max_companion.

Both packet hashes match the brief. The merge contains 86 inherited modules, with 73 shared modules, zero conflicts, and byte-identical inherited sources, including comparison against the pinned round-4 archive. Six new StackSort*6.lean modules supply the finite tagged bijection, cardinality sum, fixed-maximum restriction and sum, endpoint re-exports, and audit. No residual counting Prop is assumed. All printed endpoints use only propext, Classical.choice and Quot.sound.

See results.json for completed validation totals, PROOF.md for the constructions, STATEMENT-CORRESPONDENCE.md for both readings, and REPRODUCE.md for the resumable resource-bounded replay. The archive is stacksort-source6.zip. No self-acceptance or credit is claimed; root decides.

No child agents, git, network, browser tabs, external messages, publication, upload, or shared ledger edits were used. All writes, temporary files, caches, builds and logs are lane-local. Every Lean, leanchecker and Python process uses the RSS watchdog and the prescribed CPU, wall, memory, affinity and arena settings. No background job is retained at handback.

Validation completed: fresh extraction of the frozen source-only archive, strict serial rebuild and explicit-module leanchecker for all 92 modules. The fresh audit exactly matches the initial report: 349,566 declarations in the endpoint import closure, 1,110 local declarations, and 90 new declarations. All local metadata flags are zero; all new declaration dependencies use only the permitted three axioms. Upstream metadata is reported separately in results.json. The numerical regression matches both frozen tables at all 20 seeds, independently enumerates literal collisions through size 7, and rejects wrong unary and fixed-shuffle controls. All 86 inherited source hashes still match.

Validation limitation: the separate direct literal reductions requested in the inherited brief did not complete within the required resource limits. P 5 = 2356 hit Lean's -M3500 memory threshold with both plain decide and decide +kernel; plain decide for P 6 = 29064 was stopped by the 6 GiB RSS watchdog. Their logs are logs/direct-literal-five-rerun.log, logs/direct-literal-five-kernel.log and logs/direct-literal-six.log. These scratch attempts are outside the delivered source archive. The unconditional exactSeeds20_proved theorem proves both literal equalities through the now-proved recursion; no separate direct-enumeration kernel regression is claimed. Thus all ROUND 6 proof targets are closed, but this inherited validation item remains for root's assessment. No other proof Prop remains.
