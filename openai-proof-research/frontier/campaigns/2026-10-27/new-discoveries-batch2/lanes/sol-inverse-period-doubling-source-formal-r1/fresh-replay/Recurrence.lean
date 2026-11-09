import Algebra
set_option autoImplicit false
set_option warningAsError true
namespace InversePeriodDoubling
open PowerSeries

theorem neg_self (x : ZMod 2) : -x = x := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem coeff_fourth (P : PowerSeries (ZMod 2)) (n : ℕ) :
    (P ^ 4).coeff n = if 4 ∣ n then P.coeff (n / 4) else 0 := by
  rw [show P ^ 4 = (P ^ 2) ^ 2 by ring, coeff_square]
  by_cases h : 2 ∣ n
  · rw [ite_eq_left h, coeff_square]
    by_cases h4 : 4 ∣ n
    · rw [ite_eq_left (by omega : 2 ∣ n / 2), ite_eq_left h4]
      simp only [Nat.div_div_eq_div_mul]
    · rw [ite_eq_right (by omega : ¬ 2 ∣ n / 2), ite_eq_right h4]
  · rw [ite_eq_right h, ite_eq_right (by omega : ¬ 4 ∣ n)]

theorem quartic_coeff (n : ℕ) :
    (if 3 ≤ n then (if 4 ∣ n - 3 then u ((n - 3) / 4) else 0) else 0) +
    (if 3 ≤ n then (if 2 ∣ n - 3 then u ((n - 3) / 2) else 0) else 0) +
    u n + (if n = 1 then 1 else 0) = 0 := by
  have h := congrArg (coeff n) U_quartic
  simpa only [map_add, coeff_X_pow_mul', coeff_fourth, coeff_square, u, coeff_X,
    map_zero] using h

theorem u_even (n : ℕ) : u (2 * n) = 0 := by
  have h := quartic_coeff (2 * n)
  split_ifs at h <;> simp_all <;> omega

theorem u_four_three (n : ℕ) : u (4 * n + 3) = u n := by
  have h := quartic_coeff (4 * n + 3)
  have hn : 4 * n + 3 - 3 = 4 * n := by omega
  simp only [hn, show 3 ≤ 4 * n + 3 by omega, ite_true,
    show 4 ∣ 4 * n from dvd_mul_right 4 n,
    show 2 ∣ 4 * n by omega, Nat.mul_div_cancel_left n (by decide : 0 < 4),
    show 4 * n / 2 = 2 * n by omega, u_even, add_zero,
    show ¬ 4 * n + 3 = 1 by omega, ite_false] at h
  have hz := neg_self (u n)
  exact (eq_neg_of_add_eq_zero_right h).trans hz

theorem u_four_one (n : ℕ) (hn : 1 ≤ n) : u (4 * n + 1) = u (2 * n - 1) := by
  have h := quartic_coeff (4 * n + 1)
  have h3 : 3 ≤ 4 * n + 1 := by omega
  have h4 : ¬ 4 ∣ 4 * n + 1 - 3 := by omega
  have h2 : 2 ∣ 4 * n + 1 - 3 := by omega
  simp only [h3, ite_true, h4, ite_false, h2,
    show (4 * n + 1 - 3) / 2 = 2 * n - 1 by omega, zero_add,
    show ¬ 4 * n + 1 = 1 by omega, add_zero] at h
  have hz := neg_self (u (2 * n - 1))
  exact (eq_neg_of_add_eq_zero_right h).trans hz

theorem scalar_recurrence : ScalarRecurrence := ⟨u_even, u_four_one, u_four_three⟩

end InversePeriodDoubling
