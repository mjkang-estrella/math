import LowTail

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

theorem weighted_clamped_of_bulk (n : ℕ) (hn : 1 ≤ n)
    (hb : ∀ t : ℝ, 0 ≤ t → t ^ 2 < 2 * (n : ℝ) + 1 →
      |weightedHermite n t| ≤ sourceCoefficient n * sourceEnvelope n t)
    (x : ℝ) (hx : 0 ≤ x) :
    |weightedHermite n x| ≤ sourceCoefficient n * sourceEnvelope n (min x (sourceCutoff n)) := by
  by_cases ht : x ≤ sourceCutoff n
  · rw [min_eq_left ht]
    apply hb x hx
    have ha := sourceCutoff_pos n hn
    have hc := sourceCutoff_sq_lt n hn
    nlinarith
  · have ht' := le_of_not_ge ht
    rw [min_eq_right ht']
    by_cases h1 : n = 1
    · subst n
      exact source_low_one_global x
    by_cases h2 : n = 2
    · subst n
      exact source_low_two_global x
    exact (source_tail_abs n (by omega) x ht').trans
      (hb (sourceCutoff n) (sourceCutoff_pos n hn).le (sourceCutoff_sq_lt n hn))

theorem source_point_of_weighted (n : ℕ) (x : ℝ)
    (hb : |weightedHermite n x| ≤
      sourceCoefficient n * sourceEnvelope n (min x (sourceCutoff n))) :
    |sourceHermite n x * Real.exp (-(x ^ 2))| ≤
      sourceCoefficient n * sourceEnvelope n (min x (sourceCutoff n)) *
        Real.exp (-(x ^ 2) / 2) := by
  rw [sourceHermite_eq_value]
  have he : Real.exp (-(x ^ 2)) = Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = |weightedHermite n x| * Real.exp (-(x ^ 2) / 2) := by
      rw [he, weightedHermite, ← mul_assoc, abs_mul,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

theorem source_even_all_x (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 ≤ x) :
    |sourceHermite (2 * m) x * Real.exp (-(x ^ 2))| ≤
      sourceCoefficient (2 * m) * sourceEnvelope (2 * m) (min x (sourceCutoff (2 * m))) *
        Real.exp (-(x ^ 2) / 2) := by
  apply source_point_of_weighted
  apply weighted_clamped_of_bulk (2 * m) (by omega) ?_ x hx
  intro t ht hq
  apply source_bulk_even m t ht
  norm_num at hq ⊢
  nlinarith

theorem source_one_all_x (x : ℝ) (hx : 0 ≤ x) :
    |sourceHermite 1 x * Real.exp (-(x ^ 2))| ≤
      sourceCoefficient 1 * sourceEnvelope 1 (min x (sourceCutoff 1)) *
        Real.exp (-(x ^ 2) / 2) := by
  apply source_point_of_weighted
  apply weighted_clamped_of_bulk 1 (by omega) ?_ x hx
  intro t _ hq
  apply source_bulk_one
  norm_num at hq
  exact hq

end HermiteEnvelope
