/-
  MathDB 347063: the two endpoint theorems.

  The game is the source game of Li--Li--Miller--Mizgerd--Sun--Xia--Zhou: `n` chips of value
  `F 1` initially, not the Zeckendorf decomposition named in the MathDB record (from which no
  move is legal, as `Zeck.CS_zeckendorf_zero` records).  `phi = (1 + √5) / 2`.
-/
import ZeckCS
import ZeckSS

open Classical

namespace Zeck

/-- Split Smallest, part (a): the number of moves is `phi^2 * n + O((log n)^2)`. -/
theorem split_smallest_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(SS n : ℝ) - phi ^ 2 * n| ≤ C * (Real.log n) ^ 2 :=
  SS_estimate

/-- Combine Smallest, part (b): the number of moves is `c * n + O(√n log n)` with
`c = 5/2 - phi + ∑_{j ≥ 2} 1 / F_{2j}`. -/
theorem combine_smallest_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |(CS n : ℝ) - (5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ)) * n|
        ≤ C * Real.sqrt n * Real.log n :=
  CS_estimate

/-- The numerical bracket for the Combine Smallest constant. -/
theorem combine_constant_bracket :
    (1.206 : ℝ) < 5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ) ∧
      5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ) < 1.207 :=
  combC_bracket

end Zeck
