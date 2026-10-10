# Focused referee report: F010 unbalanced unit-circle incidences, round 2

**Verdict: ACCEPT.** The corrected `findings/F010-unbalanced-unit-incidences.md` states a correct theorem with a complete proof, given the pinned upstream bound u(N) ≤ C₀N^β₀. None of the false round-1 claims survives. The exponent choice is used consistently throughout, and every dependency is stated. Only cosmetic edits remain (§4). None affects validity.

Scope: downstream validity and honest novelty only. Upstream truth is assumed, and literature priority is not required.

## 1. Exponent convention propagation

- β = (β₀+4/3)/2 gives 1 < β < 4/3 even when β₀ = 1. Since N ≥ 1, the bound u(N) ≤ C₀N^β follows from the upstream bound. δ is defined as 4/3−β, not 4/3−β₀. I checked every later use: θ = β−1 ∈ (0,1/3), 1−β < 0, 3−2β > 0, the identity m^{2−β}n^{2β−2} = (mn)^{2/3}(m/n²)^δ, and the saving n^{εδ}. All of them refer to the chosen β. No β₀ appears after the source paragraph.
- K depends only on C₀, the chosen β, and the absolute partition, Bézout and KST constants. Calling K "absolute for the fixed upstream input" is therefore accurate.

## 2. Independent re-check of the proof

- **Step 0.** Split P′ into ⌈m′/n′⌉ ≤ 2m′/n′ groups. For each group, |G∪Q′| ≤ 2n′. Each unordered pair has at most 2 ordered preimages, and p ≠ q holds automatically. u is monotone. Together these give I ≤ 2^{2+β}C₀ m′n′^{β−1}. Overlap between P and Q is handled correctly. (∗) needs m′, n′ ≥ 1, and the proof omits empty cells to meet this.
- **Step 1.** Σ_p C(d_p,2) ≤ 2C(n,2) gives I ≤ m + O(m^{1/2}n). This matches the stated K_{2,3} orientation, and for m ≥ n² it gives I = O(m).
- **Step 2.** D = ⌊m/n⌋ satisfies m/(2n) ≤ D ≤ m/n and D² ≤ m, because m ≤ n². The case D = 1 is covered by the degeneracy paragraph.
  - **Contained circles.** Over ℂ, each circle polynomial becomes uv−1, which is irreducible. Hence at most D/2 circles lie in Z(f). Using d ≤ 1 + C(d,2), these circles contribute at most m + D²/4 ≤ 2m.
  - **Zero-set points on other circles.** Each such circle meets Z(f) in at most 2D points, contributing at most 2Dn ≤ 2m.
  - **Cells.** Each circle meets at most max(1,2D) ≤ 3D cells.
  - **Exponents.** I re-derived both: −2 + 2(2−β) + (β−1) = 1−β and 1 − 2(β−1) = 3−2β. The directions of the inequalities D ≥ m/2n and D ≤ m/n match the signs of these exponents. Both sums are O(m^{2−β}n^{2β−2}).
  - **Completeness.** The four contributions together cover every incidence exactly once or more.
- **Saving claim.** For n ≤ m ≤ n², the nonlinear term is at least m, since (n²/m)^{β−1} ≥ 1. For m ≤ n^{2−ε}, it is at most (mn)^{2/3}n^{−εδ}. The claim is correct.
- **Sharpness claim.** For m ≥ n², the nonlinear term is at most m. The circle-around-one-centre example gives I ≥ m, so Θ(m) is correct. No nonlinear lower bound is asserted for n ≤ m < n², which is correct.

## 3. Old false claims: all removed or correctly recorded as rejected

- **A1 "both r-exponents exceed 3".** Now recorded as false. A1 is no longer part of the theorem.
- **A3 comparator O(k^{2/3}n^{4/3}).** Rejected, with the grid counterexample. That example (Θ(n²) pairs from O(n/√log n) distances) is correct. No crossover claim remains.
- **β = 1+o(1) / conjectural sharpness.** Rejected on both grounds: the source reports a fixed-power superlinear lower bound, and the constants do not stay uniform as the exponent varies.
- **"Extension to k radii needs more than u(N)".** Absent.
- **Companion description and authors.** The weak-pinned paper is now named and distinguished correctly. Sharir–Sheffer–Zahl are named correctly. "Aronov" no longer appears.
- **Novelty.** The finding now calls the theorem a standard partitioning transfer whose priority is not established. This is honest and adequate.
- **Validation paragraph.** It correctly disclaims the lattice experiment and proof-assistant verification.

## 4. Remaining corrections (cosmetic, non-blocking)

1. Thin spaces have been stripped in several places, producing "Theorem4.1", "Theorems2.1–2.2", "distance1", "exceed3", "above3"/"below3" and "exponent1+o(1)". Restore the spaces.
2. Once integrated, update the Status line from "awaiting focused second review" to accepted, and link this report in the Validation section.
3. Optional: in the bullet on circles contained in Z(f), write "d_p ≤ 1 + C(d_p,2) for every integer d_p ≥ 0". The current wording, "each point has degree d_p ≤ …", reads oddly.

No mathematical corrections are required.
