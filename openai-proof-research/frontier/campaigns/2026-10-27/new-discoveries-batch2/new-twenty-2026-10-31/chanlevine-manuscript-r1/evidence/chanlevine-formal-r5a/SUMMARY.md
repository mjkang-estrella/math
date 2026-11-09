# Round 5a handback: partial, not acceptance

PrimitiveTopCoefficient and PrimitivePeriodData are now proved unconditionally. TransferCountEvaluation remains open. CountFinal4.lean proves ChanLevine.Round5.spectralOrder and unitCount conditionally on exactly Round3.TransferCountEvaluation. These are not unconditional counting endpoints and do not solve MathDB 338887. No self-acceptance or credit is requested; root decides.

## Completed proofs

CountR5Top.lean extracts the degree-one coefficient matrix z^k J from each transfer factor, where J = [[0,z],[-1,0]]. The top coefficient matrix of the r-factor product is the product of these coefficient matrices, using the frozen degree bounds. A two-step induction with J^2 = -z I gives topMatrix z (2s) = ((-1)^s z^(2s²)) I. Odd top matrices have trace zero. At e = 2s, z^(2s²) = (z^e)^s = 1. Thus the required parity coefficient follows from z^e = 1 alone; primitivity and a half-power lemma are unnecessary. This is a simplification of the proposed algebraic plan, not an extra assumption.

CountR5Inclusion.lean proves that at positive level the ORIGINAL frozen CycleTest is equivalent to the absence of an empty facing pair. It expresses the indicator as a finite product, expands that product over the powerset with an arbitrary scalar weight, and proves adjacent facing pairs are incompatible. Positivity handles both Hamiltonian clauses of the frozen predicate explicitly.

CountR5Fibre.lean constructs a finite type of literal CycleTest configurations at fixed level. Its weight fibres are equivalent to the subtypes defining testCount. It proves fourier_literal_fibre and fourier_inclusion_exclusion: the original Fourier coefficient is exactly a finite sum over all level-m configurations and all subsets of vertices of the signed empty-facing indicators, weighted by the character of the FULL frozen chipWeight. The rotor contribution is retained. These are unconditional finite counting identities, not transfer-matrix evaluations.

CountFinal4.lean supplies the unconditional primitivePeriodData and the endpoints with one explicit remaining Prop. CountR5Controls.lean has small kernel checks; CountR5Audit.lean audits the reachable declaration closure of local endpoint and control modules, including generated declarations. The frozen audit modules remain unchanged.

## Exact remaining obligation and next plan

The remaining Prop is precisely Round3.TransferCountEvaluation, defined in formal/CountSpectralModel.lean. It quantifies over every n, m, NeZero n, 3 ≤ n, 1 ≤ m, and frequency k; it equates finiteFourier of the original countVector with quotientCoeff of the n-factor transfer trace over its denominator. No new axiom or weaker replacement count has been introduced.

Continue from fourier_inclusion_exclusion rather than repeating the Fourier/fibre or local indicator work:

1. Reindex level configurations by rotors and bounded chip functions. For each selected facing-edge subset, prove the endpoints are disjoint. Sum the full rotor character to obtain z^|M| (1+z)^(n-2|M|). This is still a Lean proof obligation, though exact diagnostics check the formula for every matching through n = 10.
2. Sum chip functions with total m. Prove that the resulting finite convolution is quotientCoeff with denominator product (1-X z^k), using the literal recursive quotientCoeff definition. Treat the positive-level exclusion of the two empty constant rotors explicitly.
3. Expand the ordered transfer trace into closed state sequences and construct the cyclic matching correspondence, including the wrap edge and alternating perfect matchings. Each domino contributes -z g_k g_(k+1).
4. Combine these identities to prove TransferCountEvaluation, then apply the existing unconditional primitivePeriodData. The current conditional endpoint is not a substitute for these steps.

## Validation and limits

The archive contains the 23 frozen modules, byte-identical to the input zip with SHA-256 ced8741408ce27254232a7b351b161b5cb31110b2ebe41136613ab1556e63830, plus six new modules. Before/after hashes are recorded. Strict serial compilation and leanchecker are run per module after extraction into a new empty directory; receipts support resumption. Full logs, failures, negative controls, declaration metadata and exact Python diagnostics are retained. See results.json and REPRODUCE.md for final measured totals.

The checker retains the inherited 104 positive-level cases for 3 ≤ n ≤ 10 and 1 ≤ m ≤ 2n, and adds exact top-matrix and forced-rotor-factor checks. Numerical diagnostics do not prove general statements. The declaration audit distinguishes LOCAL flags from UPSTREAM executable metadata; upstream executable overrides are reported rather than represented as locally authored unsafe declarations. Only propext, Classical.choice and Quot.sound are permitted as reachable axioms.

All writes are lane-local. No child agents, git operations, shared-ledger edits, network, uploads, external messages or browser tabs were used. No upstream-truth audit or new novelty clearance is claimed. The pinned manuscript's Conjecture 8.3 and the prior proof/review/plan were consulted. Root alone decides acceptance.

The first development replay compiled and kernel-checked all 29 modules, then failed in Python postprocessing because a broad edit changed an audit dictionary key to a tuple. The key was corrected; the failure is retained. The source archive is produced only after correction and is replayed from a fresh extraction.
