import UlasPositive
set_option linter.unusedSimpArgs false
open PowerSeries
namespace Ulas.Round4

theorem coeff_y_factor (n : ℕ) : coeff n (y*(1+y)) = (n:ℤ) := by
  rw [one_add_y, y, mul_assoc]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul]
    simp [coeff_mul, geomStep]

theorem readout_factor_odd (m n : ℕ) (hn : n%2 = 1) :
    ¬ (2:ℤ) ∣ coeff n (C^m*(y*(1+y))) := by
  have h : (Int.cast (coeff n (C^m*(y*(1+y)))) : ZMod 2) = (n:ZMod 2) := by
    have hh := congrArg (coeff n) (show
      PowerSeries.map (Int.castRingHom (ZMod 2)) (C^m*(y*(1+y))) =
      PowerSeries.map (Int.castRingHom (ZMod 2)) (y*(1+y)) by
        rw [map_mul, C_pow_mod_two, one_mul])
    rw [coeff_map, coeff_map, coeff_y_factor] at hh
    change (Int.cast (coeff n (C^m*(y*(1+y)))) : ZMod 2) = Int.cast (n:ℤ) at hh
    simpa only [Int.cast_natCast] using hh
  intro hd
  have hz : (Int.cast (coeff n (C^m*(y*(1+y)))) : ZMod 2) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  rw [h] at hz
  have hnz : (n:ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod n 2, hn]
    rfl
  rw [hnz] at hz
  exact one_ne_zero hz

theorem val_exact_of_divisibility (z : ℤ) (a : ℕ)
    (hd : (2:ℤ)^a ∣ z) (hnd : ¬ (2:ℤ)^(a+1) ∣ z) : padicValInt 2 z = a := by
  have hz : z ≠ 0 := by intro h; simp [h] at hnd
  have hlo := ((padicValInt_dvd_iff (p := 2) a z).mp hd).resolve_left hz
  have hhi : ¬ a+1 ≤ padicValInt 2 z := by
    intro h; exact hnd ((padicValInt_dvd_iff (p := 2) (a+1) z).mpr (Or.inr h))
  omega

/-- Exact odd-index readout. No series-to-polynomial premise remains. -/
theorem exact_readout (m a n : ℕ) (R : Polynomial ℤ) (hn : n%2 = 1)
    (h0 : (2:ℤ)^a ∣ R.coeff 0) (h0' : ¬ (2:ℤ)^(a+1) ∣ R.coeff 0)
    (hhigh : ∀ E, E ≠ 0 → (2:ℤ)^(a+1) ∣ R.coeff E) :
    padicValInt 2 (coeff n (C^m*(y*(1+y)*ev R))) = a := by
  let b := C^m*(y*(1+y))
  have ht : ∀ E, (2:ℤ)^(a+1) ∣ (R-Polynomial.C (R.coeff 0)).coeff E := by
    intro E
    by_cases he : E = 0
    · simp [he]
    · simpa only [Polynomial.coeff_sub, Polynomial.coeff_C, ite_eq_right he, sub_zero] using hhigh E he
  have herr := coeff_dvd_mul_right ((2:ℤ)^(a+1)) b _ (coeff_dvd_ev _ _ ht) n
  have herr' : (2:ℤ)^(a+1) ∣ coeff n (b*ev R)-R.coeff 0*coeff n b := by
    simpa [map_sub, ev_C, mul_sub, coeff_mul_C, mul_comm] using herr
  have hb : padicValInt 2 (coeff n b) = 0 :=
    padicValInt.eq_zero_of_not_dvd (readout_factor_odd m n hn)
  have hbz : coeff n b ≠ 0 := by
    intro hz
    exact readout_factor_odd m n hn (by simp [b, hz])
  have hrz : R.coeff 0 ≠ 0 := by intro hz; simp [hz] at h0'
  have hmain : ¬ (2:ℤ)^(a+1) ∣ R.coeff 0*coeff n b := by
    intro hd
    have hv := ((padicValInt_dvd_iff (p := 2) (a+1) _).mp hd).resolve_left (mul_ne_zero hrz hbz)
    rw [padicValInt.mul hrz hbz, hb, add_zero, val_exact_of_divisibility _ a h0 h0'] at hv
    omega
  have hnd : ¬ (2:ℤ)^(a+1) ∣ coeff n (b*ev R) := by
    intro hd
    exact hmain (by simpa using dvd_sub hd herr')
  have hd : (2:ℤ)^a ∣ coeff n (b*ev R) := by
    apply coeff_dvd_mul_right
    apply coeff_dvd_ev
    intro E
    by_cases he : E = 0
    · simpa [he] using h0
    · exact dvd_trans (pow_dvd_pow _ (by omega : a ≤ a+1)) (hhigh E he)
  simpa [b, mul_assoc] using val_exact_of_divisibility _ a hd hnd
end Ulas.Round4
