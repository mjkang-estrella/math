import MatrixSeries
import Mathlib.RingTheory.PowerSeries.Log

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem derivative_logOf_mul (f : PowerSeries R) (hf : constantCoeff f = 1) :
    derivative (logOf f) * f = derivative f := by
  have hz : constantCoeff (f - 1) = 0 := by simp [hf]
  have hs := HasSubst.of_constantCoeff_zero' hz
  have hi := congrArg (fun g : PowerSeries R => g.subst (f - 1))
    (derivative_log_mul_one_add_X (A := R))
  rw [subst_mul hs, subst_add hs, subst_X hs] at hi
  have ho : (1 : PowerSeries R).subst (f - 1) = 1 := by
    change (C (1 : R)).subst (f - 1) = 1
    rw [subst_C, map_one]
  have hi2 : (derivative (log R)).subst (f - 1) * f = 1 := by
    simpa only [ho, add_sub_cancel] using hi
  rw [logOf_eq, derivative_subst hs, map_sub, derivative.map_one_eq_zero, sub_zero]
  calc
    ((derivative (log R)).subst (f - 1) * derivative f) * f =
      ((derivative (log R)).subst (f - 1) * f) * derivative f := by ring
    _ = derivative f := by rw [hi2, one_mul]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem traceLog_derivative (L : Matrix n n R) :
    derivative (-logOf ((1 - (X : PowerSeries R) • L.map C).det)) =
      tracePowerSeries L := by
  let f := (1 - (X : PowerSeries R) • L.map C).det
  have hf : constantCoeff f = 1 := determinantSeries_constantCoeff L
  have hu : IsUnit f := isUnit_iff_constantCoeff.mpr (by rw [hf]; exact isUnit_one)
  have hlog := derivative_logOf_mul f hf
  have hdet := determinantSeries_derivative L
  change derivative f = -(f * tracePowerSeries L) at hdet
  rw [hdet] at hlog
  rw [map_neg]
  apply hu.mul_right_cancel
  calc
    -(derivative (logOf f)) * f = -(derivative (logOf f) * f) := by ring
    _ = tracePowerSeries L * f := by rw [hlog]; ring


section Field
variable {K : Type*} [Field K] [CharZero K]

theorem traceLog_coefficient (L : Matrix n n K) (m : ℕ) (hm : 0 < m) :
    coeff m (-logOf ((1 - (X : PowerSeries K) • L.map C).det)) =
      Matrix.trace (L ^ m) / (m : K) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hd := congrArg (coeff k) (traceLog_derivative L)
  rw [coeff_derivative] at hd
  simp only [tracePowerSeries, coeff_mk] at hd
  apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero k)).mpr
  simpa using hd
end Field

end PeakonCoefficients
