import SourceEndpoint

set_option autoImplicit false

namespace FourProjection

/-- Four zero-rank projections in any ambient dimension, via the actual source wrapper. -/
theorem source_zero_rank_boundary {N : Type*} [Fintype N] [DecidableEq N] :
    let P : Matrix N N ℂ := 0
    let X := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (P + P)
    (Matrix.trace ((X * P * X) * (X * P * X) +
      (X * P * X) * (X * P * X))).re ≤ (Matrix.trace (P * P + P * P)).re := by
  exact banica_nechita_conjecture_6_6 0 0 0 0
    Matrix.isHermitian_zero Matrix.isHermitian_zero
    Matrix.isHermitian_zero Matrix.isHermitian_zero
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) rfl rfl

/-- Empty ambient dimension, with arbitrary named input matrices. -/
theorem source_empty_ambient_boundary (P Q R S : Matrix Empty Empty ℂ) :
    let X := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (P + R)
    let Y := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (Q + S)
    (Matrix.trace ((X * P * X) * (Y * Q * Y) +
      (X * R * X) * (Y * S * Y))).re ≤ (Matrix.trace (P * R + Q * S)).re := by
  have hzero (A : Matrix Empty Empty ℂ) : A = 0 := Subsingleton.elim _ _
  rw [hzero P, hzero Q, hzero R, hzero S]
  exact source_zero_rank_boundary

end FourProjection
