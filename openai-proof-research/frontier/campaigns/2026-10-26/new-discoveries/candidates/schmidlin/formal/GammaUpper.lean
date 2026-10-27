import GammaLimit
import GammaStep

open Filter Topology

namespace Schmidlin

theorem stirlingUpper_tendsto : Tendsto stirlingUpper atTop (nhds 0) := by
  have h : Tendsto (fun z : ℝ => z⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have ht := ((h.const_mul ((1:ℝ)/12)).sub ((h.pow 3).const_mul ((1:ℝ)/360))).add
    ((h.pow 5).const_mul ((1:ℝ)/1260))
  convert ht using 1
  · ext z
    unfold stirlingUpper
    simp only [mul_inv_rev, inv_pow, div_eq_mul_inv]
    ring
  · norm_num

theorem gammaError_le_stirlingUpper {z : ℝ} (hz : 0 < z) :
    gammaError z ≤ stirlingUpper z := by
  have ht : Tendsto (fun n : ℕ => z+(n:ℝ)) atTop atTop :=
    by simpa only [add_comm] using
      tendsto_atTop_add_const_right atTop z (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : ℕ => gammaError (z+n)-stirlingUpper (z+n)) atTop (nhds 0) := by
    simpa using (gammaError_tendsto.comp ht).sub (stirlingUpper_tendsto.comp ht)
  have hm : Monotone (fun n : ℕ => gammaError (z+n)-stirlingUpper (z+n)) := by
    apply monotone_nat_of_le_succ
    intro n
    have hp : 0 < z+(n:ℝ) := by positivity
    have hs := (upperError_strict_mono_step hp).le
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hs
  have hb (n : ℕ) : gammaError z-stirlingUpper z ≤
      gammaError (z+n)-stirlingUpper (z+n) := by
    simpa only [Nat.cast_zero, add_zero] using hm (Nat.zero_le n)
  have hbound : gammaError z-stirlingUpper z ≤ 0 :=
    ge_of_tendsto hl (Filter.Eventually.of_forall hb)
  linarith

end Schmidlin
