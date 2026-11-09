import BinaryDigits
import SourceDefs
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace JacobiShifted.DyadicArithmetic
open BinaryFiltration
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem factorial_valuation (m : ℕ) :
    padicValNat 2 m.factorial + sigma m = m := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) m
  have b := Nat.digit_sum_le 2 m
  change sigma m ≤ m at b
  change (2-1)*padicValNat 2 m.factorial = m - sigma m at h
  omega

theorem factorial_valuation_mono {a b : ℕ} (h : a ≤ b) :
    padicValNat 2 a.factorial ≤ padicValNat 2 b.factorial := by
  apply (padicValNat_dvd_iff_le (Nat.factorial_ne_zero b)).mp
  exact (pow_padicValNat_dvd (p := 2) (n := a.factorial)).trans
    (Nat.factorial_dvd_factorial h)

theorem exponent_balance {r d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    dyadicExponent r + sigma (d-1) =
      (2*r-1) + d + (padicValNat 2 ((r-1).factorial) -
        padicValNat 2 ((d-1).factorial)) := by
  have h := factorial_valuation (d-1)
  have hm := factorial_valuation_mono (a := d-1) (b := r-1) (by omega)
  unfold dyadicExponent
  omega

theorem centralBinom_valuation (m : ℕ) :
    padicValNat 2 m.centralBinom = sigma m := by
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
    (p := 2) (n := m) (k := m)
  change (2-1)*padicValNat 2 ((m+m).choose m) = sigma m+sigma m-sigma (m+m) at h
  simp only [show 2-1=1 from rfl, one_mul, ← two_mul, sigma_double] at h
  rw [Nat.centralBinom_eq_two_mul_choose]
  omega

theorem catalan_ne_zero (m : ℕ) : catalan m ≠ 0 := by
  intro h
  have he := succ_mul_catalan_eq_centralBinom m
  rw [h, mul_zero] at he
  exact (Nat.centralBinom_pos m).ne' he.symm

theorem catalan_valuation (m : ℕ) :
    padicValRat 2 (catalan m : ℚ) = (sigma m : ℤ) - padicValNat 2 (m+1) := by
  have h := congrArg (padicValNat 2) (succ_mul_catalan_eq_centralBinom m)
  rw [padicValNat.mul (by omega : m+1≠0) (catalan_ne_zero m),
    centralBinom_valuation] at h
  rw [← padicValRat_of_nat]
  omega

theorem twoLocal_iff_valuation_nonneg (q : ℚ) :
    TwoLocal q ↔ 0 ≤ padicValRat 2 q := by
  have he : Odd q.den ↔ ¬ 2 ∣ q.den := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  have hv : padicValNat 2 q.den = 0 ↔ ¬ 2 ∣ q.den := by
    simpa only [not_not] using
      (not_congr (dvd_iff_padicValNat_ne_zero q.den_ne_zero)).symm
  rw [TwoLocal, he, ← hv, padicValRat_def]
  have hc := Rat.num_or_den_zero_padicVal q Nat.prime_two
  constructor
  · intro h; simp [h]
  · intro h
    rcases hc with hc | hc
    · rw [hc] at h; omega
    · exact hc

end JacobiShifted.DyadicArithmetic
