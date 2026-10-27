import Mathlib

set_option warningAsError true

open scoped MatrixOrder ComplexOrder

namespace SquaredPolya

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The literal operator geometric mean using the positive functional-calculus square root. -/
noncomputable def geometricMean (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt A * CFC.sqrt ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) * CFC.sqrt A

theorem geometricMean_eq_of_riccati {A B X : Matrix n n ℂ}
    (hA : A.PosDef) (hX : X.PosSemidef) (hRic : X * A⁻¹ * X = B) :
    geometricMean A B = X := by
  let S := CFC.sqrt A
  let J := S⁻¹
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg A
  have hS2 : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSU : IsUnit S := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).2 hA.isUnit
  have hSdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hSU
  have hSJ : S * J = 1 := Matrix.mul_nonsing_inv S hSdet
  have hJS : J * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hJ2 : J * J = A⁻¹ := by
    rw [← hS2, Matrix.mul_inv_rev]
  have hSPSD : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hS0
  have hJ0 : 0 ≤ J := hSPSD.inv.nonneg
  have hJX : 0 ≤ J * X * J := conjugate_nonneg_of_nonneg hX.nonneg hJ0
  have hSq : (J * X * J) * (J * X * J) = J * B * J := by
    calc
      _ = J * (X * (J * J) * X) * J := by noncomm_ring
      _ = J * B * J := by rw [hJ2, hRic]
  have hRoot : CFC.sqrt (J * B * J) = J * X * J := CFC.sqrt_unique hSq hJX
  change S * CFC.sqrt (J * B * J) * S = X
  rw [hRoot]
  calc
    S * (J * X * J) * S = (S * J) * X * (J * S) := by noncomm_ring
    _ = X := by rw [hSJ, hJS, one_mul, mul_one]


end SquaredPolya
