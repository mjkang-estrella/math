import InitialValues

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

theorem abs_le_envelope_of_sq {y C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q)
    (hb : y ^ 2 * q ≤ C ^ 2) : |y| ≤ C * (Real.sqrt q)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hq)).2
  refine le_of_sq_le_sq ?_ hC
  simpa only [mul_pow, sq_abs, Real.sq_sqrt hq.le] using hb

theorem weightedHermite_one (x : ℝ) :
    weightedHermite 1 x = 2 * x * Real.exp (-(x ^ 2) / 2) := by
  norm_num [weightedHermite, hermiteValue, hermitePoly]

theorem one_bulk_exp_bound (u : ℝ) (hu : 0 ≤ u) (hq : u ≤ 3) :
    Real.pi * u * (1 - u / 3) ≤ Real.exp u := by
  have hpi : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hp : 0 ≤ u * (1 - u / 3) := mul_nonneg hu (by linarith)
  calc
    _ = Real.pi * (u * (1 - u / 3)) := by ring
    _ ≤ (22 / 7 : ℝ) * (u * (1 - u / 3)) := mul_le_mul_of_nonneg_right hpi hp
    _ ≤ 1 + u + u ^ 2 / 2 := by nlinarith [sq_nonneg (u - 9 / 13)]
    _ ≤ _ := Real.quadratic_le_exp_of_nonneg hu

theorem sourceCoefficient_one_sq : sourceCoefficient 1 ^ 2 * Real.pi = 4 := by
  rw [sourceCoefficient_one, div_pow, Real.sq_sqrt Real.pi_pos.le]
  field_simp
  norm_num

theorem source_bulk_one (x : ℝ) (hq : x ^ 2 < 3) :
    |weightedHermite 1 x| ≤ sourceCoefficient 1 * sourceEnvelope 1 x := by
  have hp := one_bulk_exp_bound (x ^ 2) (sq_nonneg x) hq.le
  have he : Real.exp (x ^ 2) * Real.exp (-(x ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hn : Real.pi * x ^ 2 * (1 - x ^ 2 / 3) * Real.exp (-(x ^ 2)) ≤ 1 := by
    calc
      _ ≤ Real.exp (x ^ 2) * Real.exp (-(x ^ 2)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = _ := he
  have hs : Real.exp (-(x ^ 2) / 2) ^ 2 = Real.exp (-(x ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hy : weightedHermite 1 x ^ 2 * (1 - x ^ 2 / 3) * Real.pi ≤ 4 := by
    calc
      _ = 4 * (Real.pi * x ^ 2 * (1 - x ^ 2 / 3) * Real.exp (-(x ^ 2))) := by
        rw [weightedHermite_one, mul_pow, mul_pow, hs]
        ring
      _ ≤ _ := by linarith
  have hb : weightedHermite 1 x ^ 2 * (1 - x ^ 2 / 3) ≤ sourceCoefficient 1 ^ 2 := by
    apply (mul_le_mul_iff_left₀ Real.pi_pos).mp
    nlinarith [sourceCoefficient_one_sq]
  have hq' : 0 < 1 - x ^ 2 / 3 := by linarith
  have h := abs_le_envelope_of_sq (sourceCoefficient_pos 1).le hq' hb
  norm_num [sourceEnvelope] at h ⊢
  exact h

end HermiteEnvelope
