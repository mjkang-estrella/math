import HSBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace FourProjection
open scoped BigOperators Matrix ComplexConjugate

theorem projection_eigenvalue_zero_or_one {N : Type*} [Fintype N] [DecidableEq N]
    (P : Matrix N N ℂ) (hP : P.IsHermitian) (hPP : P * P = P) (i : N) :
    hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
  have hd : Matrix.diagonal (fun j => (hP.eigenvalues j : ℂ)) *
      Matrix.diagonal (fun j => (hP.eigenvalues j : ℂ)) =
      Matrix.diagonal (fun j => (hP.eigenvalues j : ℂ)) := by
    have hh := congrArg (Unitary.conjStarAlgAut ℂ _ (star hP.eigenvectorUnitary)) hPP
    simpa only [map_mul, hP.conjStarAlgAut_star_eigenvectorUnitary,
      Function.comp_def] using! hh
  have he := congrArg (fun M : Matrix N N ℂ => M i i) hd
  have he' : (hP.eigenvalues i : ℂ)^2 = (hP.eigenvalues i : ℂ) := by
    simpa [Matrix.diagonal_mul_diagonal, pow_two] using he
  have hr : (hP.eigenvalues i)^2 = hP.eigenvalues i := by exact_mod_cast he'
  rcases mul_eq_zero.mp (show hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 by
    nlinarith) with hh | hh
  · exact Or.inl hh
  · exact Or.inr (by linarith)

abbrev ProjectionFrameIndex {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) := {i : N // hP.eigenvalues i = 1}

noncomputable instance projectionFrameIndex_fintype {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) : Fintype (ProjectionFrameIndex hP) :=
  Fintype.ofFinite _

noncomputable def projectionFrame {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) : Matrix N (ProjectionFrameIndex hP) ℂ :=
  fun n i => hP.eigenvectorUnitary n i.val

theorem projectionFrame_orthonormal {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) :
    Orthonormal ℂ (fun i : ProjectionFrameIndex hP =>
      (WithLp.toLp 2 (fun n => projectionFrame hP n i) : EuclideanSpace ℂ N)) := by
  have hh := hP.eigenvectorBasis.orthonormal.comp (fun i : ProjectionFrameIndex hP => i.val)
    Subtype.val_injective
  simpa only [projectionFrame, Matrix.IsHermitian.eigenvectorUnitary_apply,
    WithLp.toLp_ofLp] using! hh

theorem projectionFrame_isometry {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) :
    (projectionFrame hP)ᴴ * projectionFrame hP = 1 := by
  classical
  ext i j
  have hh := (orthonormal_iff_ite.mp (projectionFrame_orthonormal hP)) i j
  simpa [PiLp.inner_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_comm] using hh

end FourProjection
