import UlasOperator
import Mathlib.Data.ZMod.Basic

open PowerSeries
namespace Ulas
@[simp] theorem C_constant : constantCoeff C = 1 := by
  have h := C_agree 0 1 (by omega) 0 le_rfl
  simpa [G, geomStep, coeff_mul] using h

theorem w_mod_two : PowerSeries.map (Int.castRingHom (ZMod 2)) w = 1 := by
  ext n
  cases n with
  | zero => simp [w, geomStep, coeff_mul]
  | succ n =>
    simp [w, add_mul, coeff_succ_X_mul, geomStep, coeff_map]
    decide

/-- The formal series has no positive coefficient modulo two (F4). -/
theorem C_mod_two : PowerSeries.map (Int.castRingHom (ZMod 2)) C = 1 := by
  have hf : PowerSeries.map (Int.castRingHom (ZMod 2)) C =
      expand 2 (by decide) (PowerSeries.map (Int.castRingHom (ZMod 2)) C) := by
    conv_lhs => rw [C_functional]
    rw [map_mul, w_mod_two, one_mul, map_expand]
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp
    · have hcoeff := congrArg (coeff n) hf
      rw [coeff_expand] at hcoeff
      by_cases hd : 2 ∣ n
      · rw [ite_eq_left hd, ih (n/2) (by omega)] at hcoeff
        have hn' : n/2 ≠ 0 := by omega
        simpa [coeff_one, hn, hn'] using hcoeff
      · rw [ite_eq_right hd] at hcoeff
        simpa [coeff_one, hn] using hcoeff

/-- Every positive power is also one coefficientwise modulo two. -/
theorem C_pow_mod_two (m : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (C^m) = 1 := by
  rw [map_pow, C_mod_two, one_pow]

theorem c_mod_two (m n : ℕ) (hn : n ≠ 0) : (c m n : ZMod 2) = 0 := by
  have h := congrArg (coeff n) (C_pow_mod_two m)
  rw [coeff_map, coeff_one, ite_eq_right hn] at h
  exact h
end Ulas
