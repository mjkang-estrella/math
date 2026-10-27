import FormalJacobi

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix PowerSeries

variable {R : Type*} [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def matrixGeometric (L : Matrix n n R) : Matrix n n (PowerSeries R) :=
  fun i j => PowerSeries.mk fun k => (L ^ k) i j

theorem matrixGeometric_coeff (L : Matrix n n R) (i j : n) (k : ℕ) :
    PowerSeries.coeff k (matrixGeometric L i j) = (L ^ k) i j := by
  simp [matrixGeometric]

theorem matrixGeometric_inverse (L : Matrix n n R) :
    (1 - (PowerSeries.X : PowerSeries R) • L.map PowerSeries.C) * matrixGeometric L = 1 := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
    simp [Matrix.sub_apply, matrixGeometric,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  | succ k =>
    simp only [Matrix.sub_apply, map_sub, matrixGeometric_coeff]
    have ht : (PowerSeries.coeff (k + 1))
        (((PowerSeries.X : PowerSeries R) • L.map PowerSeries.C * matrixGeometric L) i j) = (L ^ (k + 1)) i j := by
      rw [Matrix.smul_mul]
      simp only [Matrix.smul_apply, smul_eq_mul, PowerSeries.coeff_succ_X_mul,
        Matrix.mul_apply, map_sum, PowerSeries.coeff_C_mul, Matrix.map_apply,
        matrixGeometric_coeff]
      rw [pow_succ']
      rfl
    rw [ht, sub_self]
    simp only [Matrix.one_apply]
    split_ifs <;> simp


noncomputable def tracePowerSeries (L : Matrix n n R) : PowerSeries R :=
  PowerSeries.mk fun k => Matrix.trace (L ^ (k + 1))

theorem trace_matrixGeometric_mul (L : Matrix n n R) :
    Matrix.trace (matrixGeometric L * L.map PowerSeries.C) = tracePowerSeries L := by
  apply PowerSeries.ext
  intro k
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum,
    Matrix.map_apply, PowerSeries.coeff_mul_C, matrixGeometric_coeff,
    tracePowerSeries, PowerSeries.coeff_mk]
  rw [pow_succ]
  rfl

theorem determinantSeries_derivative (L : Matrix n n R) :
    PowerSeries.derivative ((1 - (PowerSeries.X : PowerSeries R) •
      L.map PowerSeries.C).det) =
      -((1 - (PowerSeries.X : PowerSeries R) • L.map PowerSeries.C).det *
        tracePowerSeries L) := by
  have hd := derivation_det_of_inverse (PowerSeries.derivative (R := R))
    (1 - (PowerSeries.X : PowerSeries R) • L.map PowerSeries.C)
    (matrixGeometric L) (matrixGeometric_inverse L)
  have hm : (1 - (PowerSeries.X : PowerSeries R) • L.map PowerSeries.C).map
      PowerSeries.derivative = -L.map PowerSeries.C := by
    apply Matrix.ext
    intro i j
    simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Derivation.leibniz, Matrix.one_apply]
    split_ifs <;> simp
  rw [hm, Matrix.mul_neg, Matrix.trace_neg, trace_matrixGeometric_mul, mul_neg] at hd
  exact hd

theorem determinantSeries_constantCoeff (L : Matrix n n R) :
    PowerSeries.constantCoeff ((1 - (PowerSeries.X : PowerSeries R) •
      L.map PowerSeries.C).det) = 1 := by
  rw [RingHom.map_det]
  have hm : (PowerSeries.constantCoeff (R := R)).mapMatrix
      (1 - (PowerSeries.X : PowerSeries R) • L.map PowerSeries.C) = 1 := by
    apply Matrix.ext
    intro i j
    simp [RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  rw [hm, Matrix.det_one]

end PeakonCoefficients
