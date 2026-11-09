# MathDB 352401: Lecouvey–Lenart–Schultze Conjecture 5.5 (no broken diamond in hexagon paths)

Source: arXiv:2110.15394. Versions v1 and v2 exist; v2 (15 Feb 2022) was read in full. The paper is titled an "Extended Abstract". The full model appears in A. Schultze's PhD thesis (Albany, 2021, doi:10.54014/RM02-2FRQ), whose PDF returned **403** on 2026-11-03 and was not retried. That is a material source gap.

## Implementation

`scripts/crystal2.py` is a fresh implementation written from Definitions 3.1, 3.2, 4.1 and 4.3 and Theorem 5.3/Definition 5.1.

* Fidelity check 1: its e_i agrees with the cancelled worker's `scripts/crystal.py` on all 32032 (α, i) pairs in A_4 with |α| <= 6 (`logs/crystal-crosscheck-n5.log`).
* Fidelity check 2: the paper's Corollary 6.8 / Theorem 6.6 (K_{λµ}(t) = sum of t^{|α|} over α ∈ S^{id} with φ_i(α) = 0 for all i) is reproduced in **every** A_3 case scanned: 264 cases with |λ| <= 8 (`logs/crystal-validate-n4.log`), and 6048 cases with gaps of µ <= 3 and simple-root height <= 12 (`logs/crystal-scan68-n4-D3-H12.log`). Examples include K_{(2,2),(1^4)} = t^2 + t^4, matching the paper's Example 2.1, and K_{(3,1),(1^4)} = t^3+t^4+t^5.

The hypothesis set: (w, α) with w = id, k_j = g_j + 1 + d_j, where g = weight of α and d_j = µ_j - µ_{j+1} >= 0. Every pair (k_i, k_{i+1}) with k_j >= max(1, g_j + 1) is realizable by choosing µ.

## Literal counterexample to Conjecture 5.5 (A_3, |α| = 5)

α = (1,3) + (1,4) + 2(2,4) + (3,4), with i = 1, k_1 = 1, k_2 = 3. This is realized by λ = (7,7,5,0) and µ = (5,5,5,4) with w = id: the weight of α is (2,2,0,-4), so k_1 = 0+0+1 = 1 and k_2 = 2+0+1 = 3.

* φ_1(α) = e_1(α) ≠ 0 and φ_2(α) = e_2^3(α) ≠ 0.
* The path E_2 = e_2^{k_1} e_1^{k_1+k_2} e_2^{k_2}(α) begins with e_2^3. Its third step leaves the vertex β = (1,3) + (1,4) + 3(3,4).
* At β: e_1(β) = (1,4) + (2,3) + 3(3,4) ≠ 0 and e_2(β) = (1,2) + (1,4) + 3(3,4) ≠ 0, while e_1 e_2(β) ≃ 0 and e_2 e_1(β) ≃ 0. This is Exception BD (Definition 4.3).

So E_2 contains an edge of a broken diamond, and the edge lies inside e_2^{k_2}(α), the very path that defines φ_2(α). The path then dies at the next step (e_1 ≃ 0). Full traces are in `logs/crystal-trace.log` (inherited) and `logs/crystal-bd-n4-s9.log`.

Counts: in A_3 with |α| <= 9 there are 176 violating path-instances out of 810 hypothesis instances (63 have the BD edge in the first segment). In A_4 with |α| <= 7 there are 351 out of 3580 (`logs/crystal-bd-n5-s7.log`). **In every violation the path later dies (becomes ≃ 0 or 0). No path that completes the hexagon ever meets a BD edge** (inherited A_3 search to 12 parts; ours to |α| = 9/10 in A_3 and 7 in A_4).

Interpretation: if Conjecture 5.5 is read only for hexagons that close, the data supports it. The literal statement, which also covers the dying paths of case 2a in Theorem 5.3 (and the conjecture is stated as the basis of the proof of Theorem 5.3, including case 2a), is false at |α| = 5 in A_3. In A_3, Theorem 5.3 (read as "(a) if the inequality holds for the ordered pair; (b) if it holds for neither order") and Corollary 6.8 remain true on all instances tested. So in A_3 the violation does not affect the paper's results. This weighs toward a formulation defect rather than a substantive counterexample.

## Stronger finding: the paper's main formula fails in A_4

For λ = (5,4,4,4,0) and µ = (4,4,3,3,3) (equivalently (2,1,1,1,-3) and (1,1,0,0,0); simple-root coefficients 1,1,2,3):

* Lusztig's alternating formula gives K_{λµ}(t) = t^4 + t^5 + t^6 + t^7. The Kostka number 4 is confirmed independently by a brute-force SSYT count (`logs/crystal-case-A4.log`).
* The set {α ∈ S^{id} : φ_i(α) = 0 for all i} has 5 elements, with sizes 4, 5, 5, 6, 7. So the paper's Theorem 6.6 / Corollary 6.8 (stated as conditional on Conjectures 5.5 and 6.4) gives t^4 + 2t^5 + t^6 + t^7, which is wrong.
* The culprit is α = (1,3) + (3,4) + (3,5) + 2(4,5) with k_2 = k_3 = 1. Both φ_3φ_2(α) and φ_2φ_3(α) vanish, so the hexagon is broken on both sides. This contradicts Theorem 5.3(2a), which promises that one order survives. The two paths die without any BD edge: E_2 dies at a blocked e_3 (simple root (3,4)), and E_3 dies by exhaustion.
* A systematic scan with gaps <= 2 and height <= 8 finds 27 failing (λ, µ) in A_4 (`logs/crystal-scan68-n5-D2-H8.log`) and none at height <= 6.

This A_4 failure is **not** a violation of Conjecture 5.5 (no BD edge is involved). It shows that the source's chain "Conjecture 5.5 + Conjecture 6.4 ⇒ Theorem 5.3 ⇒ Theorem 6.6" fails somewhere besides 5.5. Possible culprits: Conjecture 6.4, or a gap in the proof of Theorem 5.3 (other exceptions such as BO1/BO2 or blocked steps). The alternative is that the extended abstract's definitions differ from the thesis's; the 403 thesis is needed to decide.

## Disposition

HOLD / parked. A literal counterexample to the MathDB statement exists and is small (A_3, five parts, hand-checkable). However, it lies only on paths that die, and the paper's results in A_3 are unaffected, so root may judge it a formulation correction. The A_4 failure of the source's main formula is the more substantive finding, but it is not the MathDB claim, and it depends on the exact definitions in the unread thesis. No novelty search beyond the web search (outputs and this note) and the author pages (sources/lenart-home.html, sources/schultze-research.html) found any later full version.
