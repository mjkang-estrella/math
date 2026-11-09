import PolynomialConvexity.Gaps
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option Elab.async false
namespace PolynomialConvexity
noncomputable section
open MeasureTheory Finset

/-- The zeta matrix of the finite linear order: no Jacobian is postulated. -/
def gapMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℝ := fun i j => if i ≤ j then 1 else 0

theorem gapMatrix_det (d : ℕ) : (gapMatrix d).det = 1 := by
  have h : (gapMatrix d).IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    exact ite_eq_right (not_le.mpr hji)
  rw [Matrix.det_of_isUpperTriangular h]
  simp [gapMatrix]

def gapLinear (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := Matrix.toLin' (gapMatrix d)

theorem gapLinear_apply {d : ℕ} (u : Fin d → ℝ) : gapLinear d u = tailSum u := by
  ext i
  simp [gapLinear, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, gapMatrix, tailSum,
    Finset.sum_filter, ite_mul]

theorem gapLinear_det (d : ℕ) : (gapLinear d).det = 1 := by
  rw [gapLinear, LinearMap.det_toLin', gapMatrix_det]

/-- An actual invertible linear map with its genuine inverse. -/
def gapEquiv (d : ℕ) : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
  LinearEquiv.ofIsUnitDet (f := gapLinear d)
    (v := Pi.basisFun ℝ (Fin d)) (v' := Pi.basisFun ℝ (Fin d))
    (by rw [LinearMap.det_toMatrix, gapLinear_det]; exact isUnit_one)

theorem gapEquiv_apply {d : ℕ} (u : Fin d → ℝ) : gapEquiv d u = tailSum u := by
  exact gapLinear_apply u

/-- Transport of actual Lebesgue measure under the descending gap map. -/
theorem gap_measurePreserving (d : ℕ) : MeasurePreserving (gapEquiv d) := by
  refine ⟨(gapEquiv d).continuous_of_finiteDimensional.measurable, ?_⟩
  change Measure.map (gapLinear d) volume = volume
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [gapLinear_det]; exact one_ne_zero)]
  simp [gapLinear_det]

end
end PolynomialConvexity
