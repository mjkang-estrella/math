# Twenty substantial findings

User direction, 2026-10-12: “Perfect. Now go for 20”. **Target: 20 total; 12 accepted, 8 remaining.** This extends the completed [first-ten milestone](TEN-FINDINGS.md); it does not restart the count.

The acceptance standard is unchanged: a complete nonroutine mathematical contribution, independently reviewed for proof and for substantiality against primary literature. Technical deductions, equivalent formulations, unproved conditionals and rediscovered results do not increase the count. All pinned OpenAI results are assumed true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Worldwide priority is not asserted.

Each newly accepted finding receives its own commit, followed by verified publication of only `openai-proof-research` to https://github.com/mjkang-estrella/math. Existing unrelated working-tree changes remain outside the project history.

## Active research

The following work is active or awaiting independent review. All active and future delegated rounds use GPT-6.1 Sol, high reasoning and Standard service, as requested by the user. See the [verified restart record](iterations/i256-standard-speed-restart.md).

- [I247: explicit quantitative scalarization](iterations/i247-quantitative-scalarization-parent-disposition.md) has a complete proposed proof. The [I251 independent proof](iterations/i251-quantitative-proof-parent-disposition.md) passed without repairs; [I256 Standard-speed contribution review](iterations/i256-quantitative-scalarization-parent-disposition.md) concluded TECHNICAL; it is retained without an acceptance increment. Quantitative disk geometry is excluded from this nomination.
- [I248: rooted-pattern packing](iterations/i248-rooted-packing-parent-disposition.md) has a complete proposed proof. The [I257 proof](iterations/i257-rooted-packing-proof-parent-disposition.md) passed without required repairs; [I258 contribution](iterations/i258-rooted-packing-parent-disposition.md) concluded TECHNICAL at Standard speed. It is not an additional accepted finding.
- **Accepted as [R017](findings/R017-ball-tube-contact-asymptotic.md):** the I249/I253/I263 sharp ball–tube nesting limit. The [I269 proof](iterations/i269-nonlinear-contact-proof-parent-disposition.md) passed without substantive repair and [I270 contribution](iterations/i270-nonlinear-contact-contribution-parent-disposition.md) concluded SUBSTANTIAL. This is one finding, covering the complete all-finite-perimeter limit.

- [I262: global uniform channel stability](iterations/i262-global-channel-stability.md) strengthens the I250/I259 spectral proposals by removing the support restriction. It proposes two-sided full-deficit control for all small measurable real channel rotations, with constants independent of channel count and spatial variation. The [I260 proof](iterations/i260-global-channel-proof-parent-disposition.md) passed with no required repair; [I261 contribution](iterations/i261-global-channel-contribution-parent-disposition.md) concluded TECHNICAL, so I262 is not accepted as a substantial finding. The earlier variants will not be counted separately. [I264](iterations/i264-weighted-neighborhood-channel-stability.md) is a new unreviewed strengthening using weighted-average closeness alone; I260/I261 remain on their unchanged I262 target. The new [I265 proof](iterations/i265-weighted-neighborhood-proof-parent-disposition.md) passed without required repairs; [I266 contribution](iterations/i266-weighted-neighborhood-contribution-parent-disposition.md) concluded TECHNICAL. The strengthened chain is retained without an acceptance increment. [I271](iterations/i271-global-fixed-profile-channel-stability.md) is a new unreviewed all-orientation extension: varying the exponent gives a global deficit-to-distance bound, removing the initial small-J hypothesis. Its completed [I272 contribution review](iterations/i272-global-fixed-profile-parent-disposition.md) concluded TECHNICAL: the global improvement is real, but the added step reduces explicitly to optimizing the stipulated sharp exponent family. It is not accepted. I266 explicitly includes the prior constructive contribution objection.

- [I267: sparser rooted packing](iterations/i267-sparser-rooted-packing-transfer.md) proposes the same rank-transfer conclusion under r^b >= n^(-1/3)(log n)^2, using self-bounding concentration and a shorter permutation exposure. This unreviewed follow-up does not override I258's prior TECHNICAL verdict and has no count increment. Its completed [I268 contribution review](iterations/i268-sparser-rooted-packing-parent-disposition.md) concluded TECHNICAL: the larger range is real, but standard optimum-witness concentration and shortened exposure do not establish a substantial new structural contribution. No independent proof gate or acceptance is claimed for the enlarged range.

- [I273 quantum discovery](iterations/i273-quantum-discovery-parent-disposition.md) completed with an unresolved GAD uniform-stability target. [I279](iterations/i279-gad-cat-state-obstruction.md) refutes its stronger summed-marginal bridge without refuting the target. [I280](iterations/i280-gad-uniform-stability-parent-disposition.md) now proves uniform amplitude control and special phase-family bounds, but leaves robust phase alignment unresolved. The completed [I281 adversarial discovery](iterations/i281-gad-adversarial-parent-disposition.md) independently confirms amplitude control and rules out several rare-cat attacks, but supplies no counterexample or full theorem. [I285](iterations/i285-phase-coercivity-parent-disposition.md) proposes a global bound for arbitrary functions of a fixed number of overlapping parity variables and arbitrary correlated amplitudes, with constants depending on parity rank but not block length. The [I288 independent contribution review](iterations/iteration288-bounded-parity-gad-contribution-standard-brief.md) is underway; no independent proof gate or acceptance is claimed. The unrestricted phase problem remains open. [I284](iterations/i284-depolarizing-stability-screen.md) credits the depolarizing stability literature and excludes a non-CP transfer.

- **Accepted as [R018](findings/R018-ball-slab-logarithmic-contact.md):** the I274/I275 logarithmic ball–slab minimum over all finite-perimeter pairs. [I277 proof review](iterations/i277-logarithmic-contact-proof-parent-disposition.md) passed without necessary repair; [I278 contribution review](iterations/i278-logarithmic-contact-contribution-parent-disposition.md) concluded SUBSTANTIAL for the singular lower passage beyond R017, with classical logarithmic contact laws explicitly credited. This is the twelfth acceptance.

- [I282 arithmetic joint-statistics discovery](iterations/i282-arithmetic-joint-statistics-parent-disposition.md) completed with a proved technical partial below total selected mass 1/2 and an explicit unpaid weighted prime-distribution estimate for the full target. No acceptance is added.

- [I283 endpoint check](iterations/i283-ball-slab-endpoint-obstruction.md) constructs a competing cylinder inside the slab and proves that R018's coefficient is not uniform as R approaches 1/3. This is a technical boundary observation, not a thirteenth finding. A moving-radius crossover lower bound and its substantiality are not established.

- [I286 quantitative Cartan–Hadamard discovery](iterations/i286-quantitative-cartan-hadamard-parent-disposition.md) completed with the global stability estimate still unproved and unrefuted. Its definition and BV-reduction checks are technical; volume-preserving ripples refute a proposed curvature-energy bridge, not the target. No acceptance is added.

- [I287 repeated-support Crouzeix discovery](iterations/iteration287-crouzeix-repeated-support-standard-brief.md) seeks a new algebraic step beyond R016 in exceptional support multiplicities. It runs at Standard speed; extending the same argument through known low-dimensional pencil results is explicitly not a substantial nomination.

Entries explicitly marked accepted contribute to the count below; all other entries are candidates or research records.

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
| 11 | [R017: sharp nonlinear ball–tube nesting cost](findings/R017-ball-tube-contact-asymptotic.md) | Independent I269 proof PASS and I270 contribution SUBSTANTIAL |
| 12 | [R018: sharp logarithmic ball–slab nesting cost](findings/R018-ball-slab-logarithmic-contact.md) | Independent I277 proof PASS and I278 contribution SUBSTANTIAL |

R017 and R018 are the two additional acceptances after reopening. Eight remain toward twenty total.
