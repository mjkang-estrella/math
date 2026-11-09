import GradingConsequences
open Matrix Unitary
open scoped BigOperators ComplexOrder
namespace FourProjection

/-- Instantiates the actual matrix theorem for every pair of finite types, including empty types. -/
theorem zero_rectangular_bound {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] :
    hsSq ((0 : Matrix I J ℂ) + 0) / 4 ≤
      (trace ((0 : Matrix I I ℂ) * 0) + trace ((0 : Matrix J J ℂ) * 0)).re / 2 := by
  have hI : ((1 : Matrix I I ℂ) + 0).PosDef := by simpa using (PosDef.one (n := I) (R := ℂ))
  have hJ : ((1 : Matrix J J ℂ) + 0).PosDef := by simpa using (PosDef.one (n := J) (R := ℂ))
  apply hermitian_spectral_bound isHermitian_zero isHermitian_zero
    (spectrum_bounds_of_posDef_shifts isHermitian_zero hI (by simpa using hI))
    (spectrum_bounds_of_posDef_shifts isHermitian_zero hJ (by simpa using hJ)) 0 0
  · constructor <;> simpa using (PosSemidef.one (n := _) (R := ℂ))
  · constructor <;> simpa using (PosSemidef.one (n := _) (R := ℂ))
  · simp

example : hsSq ((0 : Matrix (Fin 0) (Fin 3) ℂ) + 0) / 4 ≤
    (trace ((0 : Matrix (Fin 0) (Fin 0) ℂ) * 0) +
      trace ((0 : Matrix (Fin 3) (Fin 3) ℂ) * 0)).re / 2 := zero_rectangular_bound

example : hsSq ((0 : Matrix (Fin 3) (Fin 0) ℂ) + 0) / 4 ≤
    (trace ((0 : Matrix (Fin 3) (Fin 3) ℂ) * 0) +
      trace ((0 : Matrix (Fin 0) (Fin 0) ℂ) * 0)).re / 2 := zero_rectangular_bound

example : hsSq ((0 : Matrix (Fin 0) (Fin 0) ℂ) + 0) / 4 ≤
    (trace ((0 : Matrix (Fin 0) (Fin 0) ℂ) * 0) +
      trace ((0 : Matrix (Fin 0) (Fin 0) ℂ) * 0)).re / 2 := zero_rectangular_bound

/-- A concrete nonzero rectangular cross-Gram instance of the contraction bridge. -/
theorem rectangular_column_contracts :
    GramContractive (!![1; 0] : Matrix (Fin 2) (Fin 1) ℂ) := by
  let U : Matrix (Fin 2) (Fin 2) ℂ := 1
  let V : Matrix (Fin 2) (Fin 1) ℂ := !![1; 0]
  have hu : Uᴴ * U = 1 := by simp [U]
  have hv : Vᴴ * V = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [V, Matrix.mul_apply, Fin.sum_univ_two]
  simpa [U, V] using gramContractive_cross_isometries U V hu hv

end FourProjection
