# SUMMARY — pi-matrix-discovery-r3 (batch 2, solo)

**No discovery nominated. Credit requested: 0. Additional count remains 0/30
(root alone counts).** All writes confined to this lane; no shared, git, or
other-lane changes; no external contacts; reads only from public sources.

## What this lane did

Deep investigation of **MathDB 362175** (tight weighted-Frobenius commutator
bounds, Conjecture 1 of Mayumi–Kimura–Ohno–Chruściński, LAA 700 (2024) 35–49,
arXiv:2403.04199) — the strongest eligible target in the lane after honoring all
prior-lane exclusions — plus a decisive structural finding on **MathDB 343202**.

## Main results of the investigation (uncounted)

1. **Exact reduction.** With W = ω^(−1/2), X = A√ω, Y = B√ω, conjecture (14) of
   the record is *exactly* equivalent to
   ‖XWY − YWX‖_F ≤ √(w₁²+w₂²)‖X‖_F‖Y‖_F (all X,Y); (16) follows from (14);
   (15) reduces to a mixed-norm form. The rank-one case is exactly the known
   Fang–Cheng sharp result, so the open content is the all-matrix case.

2. **Post-2025 scope pinned.** Fang–Cheng (LAA 718 (2025) 1–13) proved the
   conjectures **only for rank-one matrices** (per the zbMATH review 1564.15017,
   read from the public zbMATH API). The general case was still open after it.
   Their body is closed access — an explicitly recorded novelty gate.

3. **Strong new numerical evidence.** Exact-operator alternating maximization
   (n ≤ 8, five spectrum families, thousands of trials) never violated either
   conjectured constant; the supremum equals (w₁²+w₂²) to ~8 digits in 24/30
   sweep cells, and the optimizers always converge to X supported on the top-2
   coordinate block — i.e., the global sup appears to be attained on the block
   where the statement is the authors' own proven n = 2 theorem. A counterexample
   is unlikely to be findable by local search; a proof is the open direction.
   Five concrete proof routes (convexity/extreme points, HS control, λ-shift
   triangle, peeling induction, Gram/prefix-projection) were worked and
   documented as *not closing* (discovery.md §1.5).

4. **MathDB 343202 is equivalent to the real polarization problem** (Ambrus
   thesis Conjecture 1.18). This lane proved the equivalence both ways (critical
   points of ∏⟨u_i,v⟩ on the √n-sphere ↔ inverse eigenvectors; Euler-identity
   argument; sign-pattern transfer S↔SMS). Hence that record is exactly as hard
   as a famous open problem — not a viable target; recorded so future lanes do
   not mistake it for a stand-alone linear-algebra question.

## Honest remaining gaps

- Fang–Cheng article body unread (closed access; no lawful open copy found).
- General all-matrix proof of (14)/(15) for 362175: open; two expert papers
  could not close it; this lane adds the reduction, the evidence, and the
  block-extremal observation, but no complete proof.
- 377365 (primitive integer powers) only glanced: Diophantine difficulty noted.
- Bounded prior-art searches only; no worldwide-priority claim anywhere.

## Recommendation

362175 remains the best future matrix target, but only with (a) lawful access to
the Fang–Cheng body, and (b) a genuinely new idea for the all-matrix case; the
natural next step is proving that the global supremum of ‖L_{XW} − R_{WX}‖/‖X‖_F
is attained on the top-2 block (empirically always true here).
