# Round 6a partial handback — not acceptance

TransferCountEvaluation is still OPEN. MathDB 338887 is not proved unconditionally. CountFinal5.spectralOrder and unitCount have exactly two explicit premises, MatchingCountConvolution and MatchingTraceExpansion. These are ordinary Lean Prop definitions in CountR6Bridge.lean, not postulated facts. No self-acceptance or credit is requested; root decides.

New proved results:

- CountR6Encoding.lean constructs an equivalence between the literal level fibre and bounded chip functions of exactly that total, paired with arbitrary rotors. sum_level_reindex gives the corresponding weighted finite sum identity. It proves disjointness of selected edge endpoints, their cardinality 2|M|, the bound 2|M| ≤ n, and vanishing of every nonmatching indicator. These definitions include the wrap edge on ZMod n.
- CountR6Rotor.lean proves the finite rotor sum for arbitrary disjoint forced clockwise/counterclockwise sets. rotorLocal_product identifies it with the full rotor-weight product times the forced-rotor indicator. forced_rotor_sum specializes this to cycle matchings, obtaining z^|M| (1+z)^(n−2|M|). Both alternating perfect matchings are allowed.
- CountR6Quotient.lean proves stability and the recurrence of the literal frozen Nat.rec quotientCoeff, uniqueness for that recurrence, and identification from a finite convolution with a denominator of constant coefficient 1. This is a proved algebraic tool; the configuration convolution remains open.
- CountR6Bridge.lean defines the explicit cyclic matching polynomial after denominator clearing. completedFourier has value 2 at zero and retains the frozen Fourier count at all positive levels. It proves TransferCountEvaluation from exactly the two remaining finite identities below.
- CountR6Controls.lean checks the wrap edge and both alternating perfect matchings using kernel decide, and rejects adjacent selected edges. CountR6Audit.lean audits the local import closure and its reachable type/value dependency closure, generated declarations included.

The inherited round-5a exact checker was run before the new rotor and quotient proofs. It verifies the bivariate cyclic matching expansion (including wrap and alternating matchings), the corrected rotor factor for every matching through n = 10, and the exact quotient recursion against the literal dynamic-programming counts for 104 positive-level cases, 3 ≤ n ≤ 10 and m ≤ 2n. Its degree-zero quotient is 2. These diagnostics are not general proofs.

## Exact remaining obligations and next plan

1. MatchingCountConvolution: for every n ≥ 3, frequency k and m ≥ 0, the coefficient of matchingNumerator equals the finite convolution of denominator coefficients and completedFourier. Continue from fourier_inclusion_exclusion using sum_level_reindex, discard nonmatchings by nonmatching_indicator, identify the character of the frozen chipWeight with the chip character times the rotor product, and apply forced_rotor_sum. Sum bounded chip functions with exact total. Prove geometric denominator cancellation as a finite coefficient identity. The zero-level assertion still needs a proof that only the two constant rotors survive; completedFourier merely specifies the required value and does not establish it.
2. MatchingTraceExpansion: the ordered transfer trace equals matchingNumerator. Expand the matrix product over closed Fin 2 state sequences. Delete sequences with consecutive state 1, identify each remaining 0→1→0 excursion with its cyclic selected edge, and prove bijectivity including the wrap excursion and both alternating perfect matchings. Alternatively prove a path matching recurrence with two boundary states and then close the cycle. Each selected edge contributes −z g_k g_(k+1).

quotientCoeff_of_convolution plus denominator_constant already assembles these into the ORIGINAL frozen TransferCountEvaluation. Round5's unconditional PrimitivePeriodData then gives SpectralOrder and UnitCount. No replacement semantics or count was introduced. The current packet does not close either remaining Prop.

The FINAL ASSEMBLY branch of TASK.txt is explicitly conditional on closing TransferCountEvaluation. That condition was not met, so the round-5b semantics packet was not merged and ChanLevineFinal.lean was not created. This is a counting partial handback, not a merged endpoint certificate.

## Validation and provenance

All 29 inherited round-5a modules are frozen, with before/after hashes. The verified input archive SHA-256 is ec02cc87ddb8aebb936ac46f0f8206459fcc25b1ee47651ba62e9c0d696b4afb. Seven new modules are added. Strict rebuild and leanchecker results, closure equality, LOCAL and UPSTREAM executable metadata, source hashes and measured resource usage are recorded in results.json after replay. Only propext, Classical.choice and Quot.sound are permitted as reachable axioms. Upstream executable metadata is reported separately from zero local flags. No upstream-truth or fresh novelty investigation is claimed.

All writes are lane-local. No agents, git, external messages, network, uploads, shared-ledger edits or browser tabs were used. Development failures are retained in unique logs. Replays are serial, with each child constrained to two CPUs, CPU 120 seconds, wall 140 seconds, about 6 GiB RSS, MALLOC_ARENA_MAX=2 and Lean -j1 -M3500. No heavy process is left at handback.

Replay-driver correction: a broad module-list substitution also changed the audit dictionary lookup into a tuple key. This was found while the serial replay was running and corrected in both driver copies. The first running driver retains the old in-memory code and is expected to fail after all Lean checks. The corrected driver resumes using source-manifest receipts; the archive is reissued with the corrected script. All Lean sources remain unchanged.
