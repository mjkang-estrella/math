import FrameBlocks

set_option autoImplicit false

open Matrix Unitary
open scoped BigOperators ComplexOrder
namespace FourProjection
variable {N I R J S : Type*}
  [Fintype N] [Fintype I] [Fintype R] [Fintype J] [Fintype S]
  [DecidableEq N] [DecidableEq I] [DecidableEq R] [DecidableEq J] [DecidableEq S]

/-- Banica–Nechita inequality for four actual orthonormal rectangular frames.
All normalizations are the literal ambient Moore–Penrose inverse square roots.
No rank balance or nonemptiness is assumed. Projection range-frame existence
is a separate step and is not asserted by this frame-level endpoint. -/
theorem four_frame_inequality
    (p : Matrix N I ℂ) (r : Matrix N R ℂ) (q : Matrix N J ℂ) (s : Matrix N S ℂ)
    (hp : pᴴ * p = 1) (hr : rᴴ * r = 1) (hq : qᴴ * q = 1) (hs : sᴴ * s = 1)
    (hE : Function.Injective (fromCols p r).mulVec)
    (hF : Function.Injective (fromCols q s).mulVec)
    (hpq : pᴴ * q = 0) (hrs : rᴴ * s = 0) :
    let P := p * pᴴ
    let R := r * rᴴ
    let Q := q * qᴴ
    let S := s * sᴴ
    let P' := mpInvSqrt (P + R) * P * mpInvSqrt (P + R)
    let R' := mpInvSqrt (P + R) * R * mpInvSqrt (P + R)
    let Q' := mpInvSqrt (Q + S) * Q * mpInvSqrt (Q + S)
    let S' := mpInvSqrt (Q + S) * S * mpInvSqrt (Q + S)
    (trace (P' * Q' + R' * S')).re ≤ (trace (P * R + Q * S)).re := by
  let E := fromCols p r
  let F := fromCols q s
  let A := Eᴴ * E - 1
  let B := Fᴴ * F - 1
  have hA : A.IsHermitian := (isHermitian_conjTranspose_mul_self E).sub isHermitian_one
  have hB : B.IsHermitian := (isHermitian_conjTranspose_mul_self F).sub isHermitian_one
  have hEA : 1 + A = Eᴴ * E := by dsimp only [A]; abel
  have hFB : 1 + B = Fᴴ * F := by dsimp only [B]; abel
  have hplusA : (1 + A).PosDef := by
    rw [hEA]
    exact Matrix.PosDef.conjTranspose_mul_self E hE
  have hplusB : (1 + B).PosDef := by
    rw [hFB]
    exact Matrix.PosDef.conjTranspose_mul_self F hF
  have hodd : frameSign (I := I) (R := R) *
      (cfc Real.sqrt (1 + A) * ((polarFrame E)ᴴ * polarFrame F) * cfc Real.sqrt (1 + B)) *
      frameSign (I := J) (R := S) =
      -(cfc Real.sqrt (1 + A) * ((polarFrame E)ᴴ * polarFrame F) * cfc Real.sqrt (1 + B)) := by
    rw [hEA, hFB, crossGram_reconstruction E F hE hF]
    exact frameSign_cross_odd p r q s hpq hrs
  have hbound := graded_cross_isometry_bound hA hB hplusA hplusB
    (frameGrading (I := I) (R := R)) (frameGrading (I := J) (R := S))
    frameSign_isHermitian frameSign_isHermitian
    (frameSign_gram_anticommute p r hp hr) (frameSign_gram_anticommute q s hq hs)
    (polarFrame E) (polarFrame F) (polarFrame_isometry E hE) (polarFrame_isometry F hF) hodd
  change hsSq ((polarFrame E)ᴴ * polarFrame F +
    frameSign (I := I) (R := R) * ((polarFrame E)ᴴ * polarFrame F) * frameSign (I := J) (R := S)) / 4 ≤
      (trace (A * A) + trace (B * B)).re / 2 at hbound
  dsimp only [E, F, A, B] at hbound
  rw [normalized_target_energy p r q s] at hbound
  simp only [Complex.add_re] at hbound
  rw [frame_gram_energy p r hp hr, frame_gram_energy q s hq hs] at hbound
  dsimp only
  simp only [trace_add, Complex.add_re] at hbound ⊢
  linarith

end FourProjection
