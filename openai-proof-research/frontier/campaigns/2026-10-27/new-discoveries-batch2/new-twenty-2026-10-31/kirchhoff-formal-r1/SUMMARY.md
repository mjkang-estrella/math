# MathDB 349441 — fidelity gate HOLD, zero credit

This is an incomplete investigation packet, not a Lean solution and not an accepted result. No prior refutation was identified in the bounded searches, but novelty is not cleared. Phase 2 was not started because the fidelity and prior-art gate remains unresolved. Root must adjudicate; no campaign count is changed.

Independent standard-library Fraction arithmetic reconstructs the graph and all Laplacians from scratch. It does not load the predecessor's matrices. It constructs exact 11 × 11 group inverses and Moore–Penrose inverses and checks all three group-inverse equations and all four Penrose equations. Certificates, pairwise physical solutions where compatible, and negative controls are in `outputs/exact-independent.json`.

| Reading | R_1 | R_0 | R_-1 |
|---|---:|---:|---:|
| Source (4.3), true Moore–Penrose | 515538204/7137235 | 370/3 | 21930927/278132 |
| Lemma 4.6, spectral/group inverse | 1696684/14035 | 370/3 | 1096887/11036 |
| Assignment's ordered -2 X_vw, true Moore–Penrose | 3196445304/78509585 | 370/3 | 455952503/4589178 |

Both algebraic source readings reverse the first conjectured inequality. These are ordinary exact calculations, not kernel proofs.

The assignment's claimed literal resistance formula differs from the actual source. Source (4.3) subtracts X_vw + X_wv; it does not subtract 2 X_vw. The difference matters for these nonsymmetric matrices. For example, applying the assignment's pair formula to the group inverse gives 836248944/5628035 at alpha=1, which is GREATER than 370/3, unlike the source pair sum and spectral trace. A silent replacement would therefore be a substantive statement mismatch.

The physical index is undefined on this witness under the literal potential equation (4.7). With w_i=d_i^(-2 alpha), exact multiplication gives w^T L=0. At alpha=1, w_0-w_10=-35/36, so L V=e_0-e_10 is impossible. At alpha=-1 the obstruction is 35. Only 16 of the 55 unordered pairs have compatible right-hand sides for either nonzero bias. The all-pairs sum cannot be assigned either algebraic value by this physical definition. This is a fidelity obstruction, not a numerical refutation under a third well-defined all-pairs physical index.

The current permitted HEAD requests succeeded. openai/math remains 4eaee87548250b2682affda7d05d947c05554bae. Omega is now 2bd34aa7fd7676d9c4233eeec266df8aa1541d93. Complete cached D5, Problems and preprints path scopes were screened, but they are not all authenticated at this new Omega head. HEAD changed-file responses cannot establish full current registry clearance. Journal-body and citing-work coverage also remain incomplete. See PRIOR-ART.md and GAPS.md.

All designated predecessor inputs were copied with identical hashes and verified unchanged afterward. All writes stayed in this lane. No agents, git operations, Lean calls, browser tabs, uploads, shared-ledger edits or persistent background jobs were used. `replay.py --exact-only` reproduces the diagnostic arithmetic; its default formal mode deliberately fails closed. There is no passing strict Lean replay, leanchecker receipt or all-declaration acceptance audit.
