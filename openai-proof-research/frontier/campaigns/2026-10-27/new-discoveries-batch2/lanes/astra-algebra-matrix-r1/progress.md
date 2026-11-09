# Astra algebra/matrix research — progress

2026-10-27 local date. Solo delegate; all output confined to this lane.
Read both AGENTS files, batch2 ledger, prior-campaign context, previous Pi progress and scripts. The Pi lane has no discovery.md at initial inspection; its work is preserved unchanged.

- 372905 excluded already: public p=9/4 refutation; p=2.5 numerical blowup previously diagnosed as optimizer artifact. No parameter-instance credit.
- 352327 exact matrix Shapiro endpoints (12 and 23): unresolved in inspected prior work; prior Pi rank-one and Hessian claims require verification, not assumptions.
- 332493 exact Banica–Nechita Conjecture 6.6 read in cached 1602.04456v3, including all six hypotheses and Moore–Penrose inverse square root. Considering a proof via polar orthogonalization and projection geometry. Live literature checks started.

No theorem proposed or credit requested. Next: obtain live primary-source/version and follow-up evidence; derive a source-faithful full-dimensional reduction and attack it.

## Candidate full proof found

A graded polar-frame argument now appears to prove the entire four-projection Conjecture 6.6, even without the two rank balances. The key scalar coefficient is
1-sqrt((1-a²)(1-b²))/(1+ab) ≤ a²+b² for |a|,|b|<1.
Diagonalize the two off-diagonal Gram defects, use the original orthogonality to relate entries of K and JKL, then use row/column bounds for BOTH rectangular contractions. Full derivation saved in discovery/proof.md. This is a candidate, not accepted: formalization and adversarial source/prior checks remain.

## End-of-run state

- Full ordinary proof of Conjecture 6.6 saved at `discovery/proof.md`, including an explicit reduced-SVD proof that the chosen polar frames equal the exact Moore–Penrose normalized source projections.
- `formal/ScalarCore.lean` and `formal/SpectralCore.lean`: eight strict Lean declarations covering scalar coefficient, real/complex weighted cancellation, and all finite rectangular spectral-array sums. Standard three axioms only. Fresh replay and actual declaration types recorded under `verification/`.
- Important gap: NO literal projection theorem in Lean yet. Exact remaining modules and target are in `discovery/lean-plan.md`.
- Independent numerical diagnostics check 100 complex cases, including unequal and zero ranks; every mathematical identity agrees to floating precision. This is only a check, not proof or credit.
- Primary follow-ups and closest rounding theorem inspected; no prior full resolution found within bounded search. Published 2017 source body returned403; this and incomplete citation coverage remain novelty limits.
- `discovery/review.md` records the strongest objections, their mathematical disposition, the formal gap and bounded novelty limits. It is a solo self-review, not an independent acceptance review.
- No ledger/shared/Pi-lane changes, git operations, external posting, or children. Root alone accepts/counts; current credit0.
