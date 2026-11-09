import formal.BinomialMoments
import formal.FiniteTransform
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
open Finset Polynomial Filter
open scoped Topology
namespace JacobiShifted
lemma oddIntegral_beta (n : ℕ) :
    oddIntegral ((1 - X) ^ n) = (2 : ℚ) ^ n * momentCoeff n := by
  induction n with
  | zero => simpa [momentCoeff_zero] using oddIntegral_one
  | succ n ih =>
    apply mul_left_cancel₀ (by positivity : (2 * (n : ℚ) + 3) ≠ 0)
    rw [oddIntegral_beta_recurrence, ih, pow_succ]
    linear_combination -(2 : ℚ) ^ (n + 1) * momentCoeff_succ n
lemma oddIntegral_scaled_beta (n : ℕ) :
    oddIntegral ((C (1 / 2 : ℚ) * (1 - X)) ^ n) = momentCoeff n := by
  rw [mul_pow, ← C_pow, oddIntegral_C_mul, oddIntegral_beta]
  rw [← mul_assoc, ← mul_pow]
  norm_num
lemma binomialOddSum_transform (m : ℕ) :
    binomialOddSum m / (2 : ℚ) ^ m =
      ∑ k ∈ range (m + 1), (-1 : ℚ) ^ k * (m.choose k : ℚ) * momentCoeff k := by
  have hp : (1 + X : ℚ[X]) = C 2 * (1 - C (1 / 2 : ℚ) * (1 - X)) := by
    rw [mul_sub, mul_one, ← mul_assoc, ← C_mul]
    simp only [show (2 : ℚ) * (1 / 2) = 1 by norm_num, map_one, map_ofNat]
    ring
  rw [binomialOddSum, ← oddIntegral_one_add_X, hp, mul_pow, ← C_pow,
    oddIntegral_C_mul, oddIntegral_neg_binomial]
  simp_rw [oddIntegral_scaled_beta]
  field_simp

lemma coeff_eq_tail_sub (k : ℕ) :
    (momentCoeff k : ℚ_[2]) = coeffTail k - coeffTail (k + 1) := by
  linear_combination -coeffTail_step k

lemma tail_binomial_transform (m : ℕ) :
    (∑ k ∈ range (m + 1), (-1 : ℚ_[2]) ^ k * (m.choose k : ℚ_[2]) *
      (momentCoeff k : ℚ_[2])) =
    coeffTail 0 + ∑ k ∈ range (m + 1),
      (-1 : ℚ_[2]) ^ (k + 1) * ((m + 1).choose (k + 1) : ℚ_[2]) * coeffTail (k + 1) := by
  have hext : (∑ k ∈ range (m + 1),
      (-1 : ℚ_[2]) ^ k * (m.choose k : ℚ_[2]) * coeffTail k) =
      coeffTail 0 + ∑ k ∈ range (m + 1),
        (-1 : ℚ_[2]) ^ (k + 1) * (m.choose (k + 1) : ℚ_[2]) * coeffTail (k + 1) := by
    have h := sum_range_succ' (fun k => (-1 : ℚ_[2]) ^ k *
      (m.choose k : ℚ_[2]) * coeffTail k) (m + 1)
    rw [sum_range_succ] at h
    simpa [add_comm] using h
  simp_rw [coeff_eq_tail_sub, mul_sub]
  rw [sum_sub_distrib, hext]
  rw [add_sub_assoc, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  rw [Nat.choose_succ_succ]
  push_cast
  rw [pow_succ]
  ring

/-- The final sum whose first term is one and whose other terms are even. -/
def tailUnitSum (m : ℕ) : ℚ_[2] :=
  ∑ k ∈ range (m + 1), (-1 : ℚ_[2]) ^ (k + 1) * (m.choose k : ℚ_[2]) *
    (coeffTail (k + 1) / (k + 1 : ℚ_[2]))

lemma tail_binomial_factor (m : ℕ) :
    (∑ k ∈ range (m + 1), (-1 : ℚ_[2]) ^ k * (m.choose k : ℚ_[2]) *
      (momentCoeff k : ℚ_[2])) = (m + 1 : ℚ_[2]) * tailUnitSum m := by
  rw [tail_binomial_transform, coeffTail_zero, zero_add, tailUnitSum, mul_sum]
  apply sum_congr rfl
  intro k _
  have h := congrArg (fun n : ℕ => (n : ℚ_[2])) (Nat.add_one_mul_choose_eq m k)
  push_cast at h
  have hk : (k + 1 : ℚ_[2]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hc : ((m + 1).choose (k + 1) : ℚ_[2]) =
      (m + 1 : ℚ_[2]) * (m.choose k : ℚ_[2]) / (k + 1 : ℚ_[2]) :=
    (eq_div_iff hk).2 h.symm
  rw [hc]
  ring

lemma tailUnitSum_norm (m : ℕ) : ‖tailUnitSum m‖ = 1 := by
  have hs : tailUnitSum m = 1 + ∑ k ∈ range m,
      (-1 : ℚ_[2]) ^ (k + 2) * (m.choose (k + 1) : ℚ_[2]) *
        (coeffTail (k + 2) / (k + 2 : ℚ_[2])) := by
    unfold tailUnitSum
    rw [sum_range_succ', add_comm]
    norm_num [coeffTail_one, Nat.add_assoc]
    simp only [add_assoc, one_add_one_eq_two]

  have hb : ‖∑ k ∈ range m, (-1 : ℚ_[2]) ^ (k + 2) *
      (m.choose (k + 1) : ℚ_[2]) * (coeffTail (k + 2) / (k + 2 : ℚ_[2]))‖ ≤ 1 / 2 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
    intro k _
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_nat_le_one _)).trans
      (by simpa only [Nat.cast_add, Nat.cast_ofNat] using norm_coeffTail_div_small (j := k + 2) (by omega))
  rw [hs, Padic.add_eq_max_of_ne]
  · rw [norm_one, max_eq_left (hb.trans (by norm_num))]
  · rw [norm_one]
    exact ne_of_gt (hb.trans_lt (by norm_num))


lemma rat_valuation_zero_of_norm_one {q : ℚ} (h : ‖(q : ℚ_[2])‖ = 1) :
    padicValRat 2 q = 0 := by
  have hq : (q : ℚ_[2]) ≠ 0 := by
    intro hq
    rw [hq, norm_zero] at h
    norm_num at h
  have hv := Padic.norm_eq_zpow_neg_valuation hq
  rw [h, Padic.valuation_ratCast] at hv
  have hz := (zpow_eq_one_iff_right₀ (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (2 : ℝ) ≠ 1)).1 hv.symm
  omega

/-- A proved conversion from the literal rational sum to the 2-adic unit. -/
lemma binomialOddSum_normalized_norm (m : ℕ) :
    ‖((binomialOddSum m / ((2 : ℚ) ^ m * (m + 1 : ℚ)) : ℚ) : ℚ_[2])‖ = 1 := by
  have ht := congrArg (fun q : ℚ => (q : ℚ_[2])) (binomialOddSum_transform m)
  push_cast at ht
  rw [tail_binomial_factor] at ht
  have hn : (m + 1 : ℚ_[2]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have he : ((binomialOddSum m / ((2 : ℚ) ^ m * (m + 1 : ℚ)) : ℚ) : ℚ_[2]) =
      tailUnitSum m := by
    push_cast
    rw [← div_div, ht]
    field_simp
  rw [he, tailUnitSum_norm]

/-- Primary Theorem 1.4 for every natural index, including zero. -/
theorem binomialOddSum_valuation (m : ℕ) :
    padicValRat 2 (binomialOddSum m) = (m : ℤ) + (padicValNat 2 (m + 1) : ℤ) := by
  have h := rat_valuation_zero_of_norm_one (binomialOddSum_normalized_norm m)
  have htwo : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn : (m + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [padicValRat.div (binomialOddSum_ne_zero m) (mul_ne_zero htwo hn),
    padicValRat.mul htwo hn, padicValRat.pow] at h
  have hnat : padicValRat 2 (m + 1 : ℚ) = (padicValNat 2 (m + 1) : ℤ) := by
    exact_mod_cast padicValRat.of_nat (p := 2) (n := m + 1)
  have hv2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using (padicValRat.self (p := 2) (by norm_num : 1 < (2 : ℕ)))
  rw [hnat, hv2] at h
  norm_num at h
  omega

end JacobiShifted
