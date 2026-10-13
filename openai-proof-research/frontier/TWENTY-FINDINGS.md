# Twenty substantial findings

User direction, 2026-10-12: “Perfect. Now go for 20”. **Target: 20 total; 10 accepted, 10 remaining.** This extends the completed [first-ten milestone](TEN-FINDINGS.md); it does not restart the count.

The acceptance standard is unchanged: a complete nonroutine mathematical contribution, independently reviewed for proof and for substantiality against primary literature. Technical deductions, equivalent formulations, unproved conditionals and rediscovered results do not increase the count. All pinned OpenAI results are assumed true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Worldwide priority is not asserted.

Each newly accepted finding receives its own commit, followed by verified publication of only `openai-proof-research` to https://github.com/mjkang-estrella/math. Existing unrelated working-tree changes remain outside the project history.

## Active research

The following work is active or awaiting independent review. All active and future delegated rounds use GPT-6.1 Sol, high reasoning and Standard service, as requested by the user. See the [verified restart record](iterations/i256-standard-speed-restart.md).

- [I247: explicit quantitative scalarization](iterations/i247-quantitative-scalarization-parent-disposition.md) has a complete proposed proof. The [I251 independent proof](iterations/i251-quantitative-proof-parent-disposition.md) passed without repairs; [I256 Standard-speed contribution review](iterations/i256-quantitative-scalarization-parent-disposition.md) concluded TECHNICAL; it is retained without an acceptance increment. Quantitative disk geometry is excluded from this nomination.
- [I248: rooted-pattern packing](iterations/i248-rooted-packing-parent-disposition.md) has a complete proposed proof. The [I257 proof](iterations/i257-rooted-packing-proof-parent-disposition.md) passed without required repairs; [I258 contribution](iterations/i258-rooted-packing-parent-disposition.md) concluded TECHNICAL at Standard speed. It is not an additional accepted finding.
- [I249/I253/I263: nested geometric contact](iterations/i263-contact-lower-bound-parent-disposition.md) now has a complete proposed nonlinear lower bound and matching recovery. [I269 proof review](iterations/iteration269-nonlinear-contact-proof-standard-brief.md) is running at Standard speed. The separate [I270 contribution review](iterations/iteration270-nonlinear-contact-contribution-standard-brief.md) is running at Standard speed; no substantial finding is accepted.

- [I262: global uniform channel stability](iterations/i262-global-channel-stability.md) strengthens the I250/I259 spectral proposals by removing the support restriction. It proposes two-sided full-deficit control for all small measurable real channel rotations, with constants independent of channel count and spatial variation. The [I260 proof](iterations/i260-global-channel-proof-parent-disposition.md) passed with no required repair; [I261 contribution](iterations/i261-global-channel-contribution-parent-disposition.md) concluded TECHNICAL, so I262 is not accepted as a substantial finding. The earlier variants will not be counted separately. [I264](iterations/i264-weighted-neighborhood-channel-stability.md) is a new unreviewed strengthening using weighted-average closeness alone; I260/I261 remain on their unchanged I262 target. The new [I265 proof](iterations/i265-weighted-neighborhood-proof-parent-disposition.md) passed without required repairs; [I266 contribution](iterations/i266-weighted-neighborhood-contribution-parent-disposition.md) concluded TECHNICAL. The strengthened chain is retained without an acceptance increment. I266 explicitly includes the prior constructive contribution objection.

- [I267: sparser rooted packing](iterations/i267-sparser-rooted-packing-transfer.md) proposes the same rank-transfer conclusion under r^b >= n^(-1/3)(log n)^2, using self-bounding concentration and a shorter permutation exposure. This unreviewed follow-up does not override I258's prior TECHNICAL verdict and has no count increment. Its [I268 contribution review](iterations/iteration268-sparser-rooted-packing-contribution-standard-brief.md) is now running at Standard speed.

These are candidates and research records, not additional accepted results.

## Accepted count

The original ten retain their existing acceptance decisions. Their linked records and first-ten ledger retain the proof and contribution evidence. Any commit IDs shown are local; filtered publication rewrites them.

| Count | Finding | Acceptance evidence |
|---|---|---|
| 1 | [R006: fixed-progression PD law and primitive roots](findings/R006-progression-PD-primitive-root-density.md) | First-ten ledger |
| 2 | [R008: parity and factor-size independence](findings/R008-parity-PD-independence.md) | First-ten ledger |
| 3 | [R009: variable-channel weighted capacity](findings/R009-variable-channel-capacity.md) | First-ten ledger |
| 4 | [R010: factor-count residues and PD independence](findings/R010-complex-modes-PD-independence.md) | First-ten ledger |
| 5 | [R011: rooted matching entropy](findings/R011-rooted-matching-entropy.md) | Linked acceptance record |
| 6 | [R012: uniform Gaussian propeller stability](findings/R012-uniform-gaussian-propeller-stability.md) | Linked acceptance record |
| 7 | [R013: higher-dimensional logarithmic stability](findings/R013-higher-dimensional-logarithmic-stability.md) | Linked acceptance record |
| 8 | [R014: dimension-uniform coefficient extraction](findings/R014-uniform-coefficient-extraction.md) | Linked acceptance record |
| 9 | [R015: tetrahedral cylinder-cover lower bound](findings/R015-tetrahedral-cylinder-lower-bound.md) | Linked acceptance record |
| 10 | [R016: complete Crouzeix equality in dimension four](findings/R016-complete-crouzeix-equality.md) | `1c8aa3f0`; independent I245 proof PASS and I246 contribution SUBSTANTIAL |

No additional result is accepted at reopening.
