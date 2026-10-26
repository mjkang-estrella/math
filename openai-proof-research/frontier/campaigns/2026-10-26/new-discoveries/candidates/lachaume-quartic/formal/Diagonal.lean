import Quartic

open Set

namespace Lachaume

noncomputable def fourthRoot (y : ℝ) : ℝ := y ^ (1 / 4 : ℝ)
noncomputable def diagonal (x : ℝ) : ℝ := fourthRoot (quartic x)
noncomputable def diagonalFirst (x : ℝ) : ℝ := first x * (1 / 4 : ℝ) * quartic x ^ (-3 / 4 : ℝ)
noncomputable def diagonalSecond (x : ℝ) : ℝ :=
  quartic x ^ (-7 / 4 : ℝ) / 16 * (4 * quartic x * second x - 3 * first x ^ 2)

theorem fourthRoot_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ fourthRoot y :=
  Real.rpow_nonneg hy _

theorem fourthRoot_fourth {y : ℝ} (hy : 0 ≤ y) : fourthRoot y ^ 4 = y := by
  unfold fourthRoot
  rw [← Real.rpow_mul_natCast hy]
  norm_num

theorem rational_lt_fourthRoot {a y : ℝ} (_ha : 0 ≤ a) (hy : 0 ≤ y)
    (h : a ^ 4 < y) : a < fourthRoot y := by
  have hh := fourthRoot_nonneg hy
  have hp := fourthRoot_fourth hy
  by_contra hn
  have hc : fourthRoot y ≤ a := le_of_not_gt hn
  have := pow_le_pow_left₀ hh hc 4
  nlinarith

theorem fourthRoot_lt_rational {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (h : y < a ^ 4) : fourthRoot y < a := by
  have hh := fourthRoot_nonneg hy
  have hp := fourthRoot_fourth hy
  by_contra hn
  have hc : a ≤ fourthRoot y := le_of_not_gt hn
  have := pow_le_pow_left₀ ha hc 4
  nlinarith

theorem hasDerivAt_diagonal {x : ℝ} (hx : 0 < x) :
    HasDerivAt diagonal (diagonalFirst x) x := by
  have hd := (hasDerivAt_quartic x).rpow_const (p := (1 / 4 : ℝ))
    (Or.inl (ne_of_gt (quartic_pos hx)))
  change HasDerivAt (fun y : ℝ => quartic y ^ (1 / 4 : ℝ)) (diagonalFirst x) x
  convert hd using 1
  norm_num [diagonalFirst]

theorem hasDerivAt_diagonalFirst {x : ℝ} (hx : 0 < x) :
    HasDerivAt diagonalFirst (diagonalSecond x) x := by
  have hp := quartic_pos hx
  have hr := (hasDerivAt_quartic x).rpow_const (p := (-3 / 4 : ℝ))
    (Or.inl (ne_of_gt hp))
  have ht : quartic x ^ (-3 / 4 : ℝ) = quartic x ^ (-7 / 4 : ℝ) * quartic x := by
    calc
      quartic x ^ (-3 / 4 : ℝ) = quartic x ^ ((-7 / 4 : ℝ) + 1) := by norm_num
      _ = quartic x ^ (-7 / 4 : ℝ) * quartic x ^ (1 : ℝ) := Real.rpow_add hp _ _
      _ = _ := by rw [Real.rpow_one]
  convert (((hasDerivAt_first x).mul_const (1 / 4 : ℝ)).mul hr) using 1
  · rfl
  · dsimp [diagonalSecond]
    norm_num at *
    rw [ht]
    ring

theorem diagonalSecond_nonpos {x : ℝ} (hx : 0 < x) : diagonalSecond x ≤ 0 := by
  unfold diagonalSecond
  rw [laguerre_identity]
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact div_nonneg (Real.rpow_nonneg (le_of_lt (quartic_pos hx)) _) (by norm_num)
  · nlinarith [sq_nonneg (x ^ 2 - 1)]

theorem diagonal_concave : ConcaveOn ℝ (Ioi 0) diagonal := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := diagonalFirst) (f'' := diagonalSecond)
    (convex_Ioi 0)
  · exact fun x hx => (hasDerivAt_diagonal hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_diagonal (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_diagonalFirst (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact diagonalSecond_nonpos (interior_subset hx)

end Lachaume
