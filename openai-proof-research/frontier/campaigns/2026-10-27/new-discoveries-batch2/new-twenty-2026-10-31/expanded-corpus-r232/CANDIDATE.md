# CANDIDATE.md: expanded-corpus-r232

**No candidate is proposed.** No UNCOMPILED Lean plan is attached, because no reserved record survived prior-art and significance screening.

## Closest items, and why they are not candidates

1. **353231: EPRS fence mesicity (refuted, but already public).**
   - The counterexample is F̆(3¹¹), n = 32. The seed ideal has bitmask 871366655 in `logs/fence-a3-t11.log`, and its rowmotion orbit has length 237 with Σ|I| = 3810 ≠ 16·237.
   - A Lean certificate would be easy: list the 237 ideals and check by `decide` that each one is a down-set, that ρ maps each to the next, and that the sum is 3810.
   - It is already public with a Lean formalization (`Aurantium-47/fence-rowmotion-counterexample`, created 2026-10-13), so it earns zero credit. Do not formalize.

2. **382066: strongly chordal ⇒ flag-accurate (open).** No counterexample exists through n = 10. Both a proof and a refutation need freeness of hyperplane arrangements (Terao's factorization; Stanley's chordal freeness), which mathlib lacks. Not Lean-feasible in this campaign.

3. **353252: weighted SE(s) spread bound (open).** A counterexample would be Lean-cheap: rational Laplacians, explicit test vectors orthogonal to 1, Rayleigh-quotient upper bounds, and monotonicity of x + y − 2xy/n below n/2. None was found; numerically the bound is tight on SE(s).

## Suggested follow-up for root

If a later lane revisits 382066, test the induction lemma recorded in `results.json`. If it holds, the ordinary proof would be short, but the Lean cost stays prohibitive.
