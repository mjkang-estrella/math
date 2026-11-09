import RangeFrames
import FrameInequality
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

open scoped Matrix
namespace FourProjection
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The literal projection endpoint, stronger than Conjecture 6.6 by omission
of both rank balances. No frames or analytic bridge are supplied as hypotheses. -/
theorem four_projection_inequality
    (P Q R S : Matrix N N ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hR : R.IsHermitian) (hS : S.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hRR : R * R = R) (hSS : S * S = S)
    (hPQ : P * Q = 0) (hRS : R * S = 0)
    (hPR : LinearMap.range P.mulVecLin ⊓ LinearMap.range R.mulVecLin = ⊥)
    (hQS : LinearMap.range Q.mulVecLin ⊓ LinearMap.range S.mulVecLin = ⊥) :
    let X := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (P + R)
    let Y := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (Q + S)
    let P' := X * P * X
    let Q' := Y * Q * Y
    let R' := X * R * X
    let S' := Y * S * Y
    (Matrix.trace (P' * Q' + R' * S')).re ≤
      (Matrix.trace (P * R + Q * S)).re := by
  classical
  have h := four_frame_inequality
    (projectionFrame hP) (projectionFrame hR)
    (projectionFrame hQ) (projectionFrame hS)
    (projectionFrame_isometry hP) (projectionFrame_isometry hR)
    (projectionFrame_isometry hQ) (projectionFrame_isometry hS)
    (projectionPairFrame_injective hP hR hPP hRR hPR)
    (projectionPairFrame_injective hQ hS hQQ hSS hQS)
    (projectionFrames_cross_eq_zero hP hQ hPP hQQ hPQ)
    (projectionFrames_cross_eq_zero hR hS hRR hSS hRS)
  dsimp only at h ⊢
  simpa only [projectionFrame_mul_adjoint hP hPP,
    projectionFrame_mul_adjoint hQ hQQ, projectionFrame_mul_adjoint hR hRR,
    projectionFrame_mul_adjoint hS hSS, mpInvSqrt] using h

/-- Banica–Nechita, arXiv:1602.04456v3, printed p.20, Conjecture 6.6.
The two rank balances are the source's ordinary finite matrix ranks. -/
theorem banica_nechita_conjecture_6_6
    (P Q R S : Matrix N N ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hR : R.IsHermitian) (hS : S.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hRR : R * R = R) (hSS : S * S = S)
    (hPQ : P * Q = 0) (hRS : R * S = 0)
    (hPR : LinearMap.range P.mulVecLin ⊓ LinearMap.range R.mulVecLin = ⊥)
    (hQS : LinearMap.range Q.mulVecLin ⊓ LinearMap.range S.mulVecLin = ⊥)
    (_hRankPQRS : P.rank + Q.rank = R.rank + S.rank)
    (_hRankPRQS : P.rank + R.rank = Q.rank + S.rank) :
    let X := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (P + R)
    let Y := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (Q + S)
    let P' := X * P * X
    let Q' := Y * Q * Y
    let R' := X * R * X
    let S' := Y * S * Y
    (Matrix.trace (P' * Q' + R' * S')).re ≤
      (Matrix.trace (P * R + Q * S)).re :=
  four_projection_inequality P Q R S hP hQ hR hS hPP hQQ hRR hSS hPQ hRS hPR hQS

end FourProjection
