import UlasEven5Coefficients
set_option linter.unusedSimpArgs false
open Polynomial
namespace Ulas.Even5
open Ulas.Round4

theorem central_valuation (a : ℕ) :
    padicValNat 2 ((2*a).choose a) = (Nat.digits 2 a).sum := by
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
    (p := 2) (n := a) (k := a)
  by_cases ha : a = 0
  · subst a; norm_num at *
  · have hd := Nat.digits_base_mul (b := 2) (m := a) (by decide) (by omega)
    rw [show a+a=2*a by omega, hd] at h
    simp only [List.sum_cons, zero_add] at h
    norm_num at h
    omega

theorem choose_kummer_bound (k a : ℕ) (hk : 1 ≤ k) (ha : a < k) :
    padicValNat 2 k ≤ padicValNat 2 ((k+a).choose (2*a+1)) + a := by
  have hid := binomial_kummer_identity k a hk
  have hz : (k+a).choose (2*a+1) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hc : (2*a).choose a ≠ 0 := Nat.choose_ne_zero (by omega)
  have h1 : (k+a).choose a ≠ 0 := Nat.choose_ne_zero (by omega)
  have h2 : (k-1).choose a ≠ 0 := Nat.choose_ne_zero (by omega)
  have hv := congrArg (padicValNat 2) hid
  rw [padicValNat.mul (mul_ne_zero hz (by omega)) hc,
      padicValNat.mul hz (by omega),
      padicValNat.mul (mul_ne_zero (by omega) h1) h2,
      padicValNat.mul (by omega) h1] at hv
  have ho : ¬ 2 ∣ 2*a+1 := by omega
  rw [padicValNat.eq_zero_of_not_dvd ho, central_valuation] at hv
  have hs := Nat.digit_sum_le 2 a
  omega

theorem u_coeff_dvd (k E : ℕ) (hk : 1 ≤ k) :
    (2:ℤ)^(padicValNat 2 k+E) ∣ (u ((k:ℤ)-1)).coeff E := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hm : ((m+1:ℕ):ℤ)-1 = m := by push_cast; ring
  rw [hm, coeff_u]
  by_cases he : E < m+1
  · have hb := choose_kummer_bound (m+1) E (by omega) he
    have hz : (m+E+1).choose (2*E+1) ≠ 0 := Nat.choose_ne_zero (by omega)
    have hv : padicValNat 2 ((2:ℕ)^(2*E)*(m+E+1).choose (2*E+1)) =
        2*E+padicValNat 2 ((m+E+1).choose (2*E+1)) := by
      rw [padicValNat.mul (by positivity) hz, padicValNat.prime_pow]
    have hd := (padicValNat_dvd_iff_le (by positivity :
      (2:ℕ)^(2*E)*(m+E+1).choose (2*E+1) ≠ 0)).mpr
      (show padicValNat 2 (m+1)+E ≤ padicValNat 2
        ((2:ℕ)^(2*E)*(m+E+1).choose (2*E+1)) by
          rw [hv]; rw [show m+1+E = m+E+1 by omega] at hb; omega)
    exact_mod_cast hd
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
end Ulas.Even5
