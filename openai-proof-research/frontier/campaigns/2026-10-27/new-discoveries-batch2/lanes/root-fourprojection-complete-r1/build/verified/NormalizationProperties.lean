import RangeFrames
import PolarFrameBridge

set_option autoImplicit false

namespace FourProjection
open scoped Matrix

theorem frameSelectorLeft_isHermitian (I J : Type*) [DecidableEq I] :
    (frameSelectorLeft I J).IsHermitian := by
  show (frameSelectorLeft I J)ᴴ = frameSelectorLeft I J
  simp [frameSelectorLeft, Matrix.fromBlocks_conjTranspose]

theorem frameSelectorLeft_idempotent (I J : Type*)
    [Fintype I] [Fintype J] [DecidableEq I] :
    frameSelectorLeft I J * frameSelectorLeft I J = frameSelectorLeft I J := by
  simp [frameSelectorLeft, Matrix.fromBlocks_multiply]

/-- The literal first normalized source operator is an orthogonal projection. -/
theorem normalized_source_projection {N : Type*} [Fintype N] [DecidableEq N]
    {P R : Matrix N N ℂ} (hP : P.IsHermitian) (hR : R.IsHermitian)
    (hPP : P * P = P) (hRR : R * R = R)
    (hdisj : LinearMap.range P.mulVecLin ⊓ LinearMap.range R.mulVecLin = ⊥) :
    let P' := mpInvSqrt (P + R) * P * mpInvSqrt (P + R)
    P'.IsHermitian ∧ P' * P' = P' := by
  classical
  have hh := normalized_congruence_is_projection (projectionPairFrame hP hR)
    (projectionPairFrame_injective hP hR hPP hRR hdisj)
    (frameSelectorLeft (ProjectionFrameIndex hP) (ProjectionFrameIndex hR))
    (frameSelectorLeft_isHermitian _ _) (frameSelectorLeft_idempotent _ _)
  dsimp only at hh ⊢
  rw [projectionPairFrame_mul_adjoint hP hR hPP hRR,
      projectionPairFrame_selector_left hP hR hPP] at hh
  exact hh

end FourProjection
