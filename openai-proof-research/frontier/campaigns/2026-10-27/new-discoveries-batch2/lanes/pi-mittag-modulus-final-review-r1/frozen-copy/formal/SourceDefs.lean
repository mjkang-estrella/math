import SeriesConvergence

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace MittagModulus

theorem mittagLeffler_even_odd {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    mittagLeffler a b z = mittagLeffler (2 * a) b (z ^ 2) +
      z * mittagLeffler (2 * a) (a + b) (z ^ 2) := by
  have hs := mittag_complex_series_summable ha hb z
  have hse := hs.comp_injective (show Function.Injective (fun n : ℕ => 2 * n) by intro i j h; dsimp at h; omega)
  have hso := hs.comp_injective (show Function.Injective (fun n : ℕ => 2 * n + 1) by intro i j h; dsimp at h; omega)
  unfold mittagLeffler
  rw [← tsum_even_add_odd hse hso, ← tsum_mul_left]
  congr 1
  · apply tsum_congr
    intro n
    have he : a * (↑(2 * n) : ℝ) + b = 2 * a * (n : ℝ) + b := by push_cast; ring
    rw [he, pow_mul]
  · apply tsum_congr
    intro n
    have he : a * (↑(2 * n + 1) : ℝ) + b = 2 * a * (n : ℝ) + (a + b) := by
      push_cast
      ring
    rw [he, pow_succ, pow_mul]
    ring

/-- The literal real expression in Conjecture3 / Eq5.2, using genuine convergent series. -/
noncomputable def sourceExpression (a t : ℝ) : ℝ :=
  Complex.normSq (mittagLeffler (2 * a) 1 (-t)) +
    t * Complex.normSq (mittagLeffler (2 * a) (1 + a) (-t))

def CompletelyMonotonePositive (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (↑(⊤ : ℕ∞)) f (Set.Ioi 0) ∧
    ∀ k : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1 : ℝ) ^ k * iteratedDeriv k f t

def SourceClaim370772 : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → CompletelyMonotonePositive (sourceExpression a)

end MittagModulus
