import TraceLog

set_option autoImplicit false
set_option maxRecDepth 2000
set_option warningAsError true

namespace PeakonCoefficients

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem coeff_pow_vanish (f : PowerSeries K) (hf : constantCoeff f = 0)
    (m j : ℕ) (hmj : m < j) : coeff m (f ^ j) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hmj)
    (le_order_pow_of_constantCoeff_eq_zero j hf)

omit [CharZero K] in
theorem coeff_subst_truncated (f g : PowerSeries K) (hg : constantCoeff g = 0) (m : ℕ) :
    coeff m (f.subst g) =
      ∑ j ∈ Finset.range (m + 1), coeff j f * coeff m (g ^ j) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra hnot
  have hmj : m < j := by simpa using hnot
  have hz := coeff_pow_vanish g hg m j hmj
  exact hj (by dsimp; rw [hz, mul_zero])

theorem coeff_negative_log (f : PowerSeries K) (hf : constantCoeff f = 0) (m : ℕ) :
    coeff m (-logOf (1 - f)) =
      ∑ j ∈ Finset.range m, coeff m (f ^ (j + 1)) / (j + 1 : K) := by
  have hsub : (1 - f : PowerSeries K) - 1 = -f := by ring
  rw [map_neg, logOf_eq, hsub, coeff_subst_truncated _ _ (by simp [hf])]
  rw [← Finset.sum_neg_distrib, Finset.sum_range_succ']
  simp only [coeff_log, ↓reduceIte, zero_mul, neg_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    map_div₀, map_pow, map_neg, map_one, map_natCast]
  rw [show -f = (-1 : K) • f by simp, _root_.smul_pow, coeff_smul, smul_eq_mul]
  have hp : ((-1 : K) ^ (j + 1)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (j + 1) 2, pow_mul]
    simp
  rw [pow_succ (-1 : K) (j + 1)]
  calc
    _ = ((-1 : K) ^ (j + 1)) ^ 2 * (coeff m (f ^ (j + 1)) / (j + 1 : K)) := by push_cast; ring
    _ = _ := by rw [hp, one_mul]

end PeakonCoefficients
