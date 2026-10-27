import Arrowhead
import SpectralCompression
import SpectralPropagation

open Finset Matrix
open scoped RealInnerProductSpace
namespace FlatBernoulli
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_inner_dot (A : Matrix (Option ι) (Option ι) ℝ)
    (x : EuclideanSpace ℝ (Option ι)) :
    ⟪x,A.toEuclideanLin x⟫ = x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, dotProduct_comm]

theorem matrix_eigenvector_action {A : Matrix (Option ι) (Option ι) ℝ}
    (hA : A.IsHermitian) (i : Option ι) :
    A.toEuclideanLin (hA.eigenvectorBasis i) = hA.eigenvalues i • hA.eigenvectorBasis i := by
  apply PiLp.ext
  intro j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

theorem arrowhead_spectral_interval (t r s : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hr : ∑ i, r i^2 = 1) (hs : ∀ i, s i^2 = 1-t i)
    (i : Option ι) :
    -1 ≤ (arrowhead_isHermitian t (fun j => s j*r j)).eigenvalues i ∧
    (arrowhead_isHermitian t (fun j => s j*r j)).eigenvalues i ≤ 1 := by
  let H := arrowhead t (fun j => s j*r j)
  let hH := arrowhead_isHermitian t (fun j => s j*r j)
  let x := hH.eigenvectorBasis i
  have hn : x.ofLp ⬝ᵥ x.ofLp = 1 := by
    calc
      _ = ⟪x,x⟫ := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [star_trivial]
      _ = 1 := by
        rw [real_inner_self_eq_norm_sq, hH.eigenvectorBasis.orthonormal.norm_eq_one]
        norm_num
  have hq : x.ofLp ⬝ᵥ (H *ᵥ x.ofLp) = hH.eigenvalues i := by
    rw [← matrix_inner_dot, matrix_eigenvector_action hH,
      real_inner_smul_right, real_inner_self_eq_norm_sq,
      hH.eigenvectorBasis.orthonormal.norm_eq_one]
    ring
  have hu : 0 ≤ x.ofLp ⬝ᵥ x.ofLp - x.ofLp ⬝ᵥ (H *ᵥ x.ofLp) := by
    rw [arrowhead_upper_sos t r s hr hs]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hl : 0 ≤ x.ofLp ⬝ᵥ x.ofLp + x.ofLp ⬝ᵥ (H *ᵥ x.ofLp) := by
    rw [arrowhead_lower_sos t r s hr hs]
    exact add_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ =>
        mul_nonneg (ht j) (sq_nonneg _)))
  rw [hn,hq] at hu hl
  constructor <;> linarith

def centerFunctional : EuclideanSpace ℝ (Option ι) →ₗ[ℝ] ℝ where
  toFun x := x none
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem arrowhead_negative_index_unique (t v : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (i j : Option ι)
    (hi : (arrowhead_isHermitian t v).eigenvalues i < 0)
    (hj : (arrowhead_isHermitian t v).eigenvalues j < 0) : i=j := by
  let H := arrowhead t v
  let hH := arrowhead_isHermitian t v
  apply negative_eigenindex_unique H.toEuclideanLin centerFunctional ?_
    hH.eigenvectorBasis hH.eigenvalues (matrix_eigenvector_action hH) i j hi hj
  intro z hz
  rw [matrix_inner_dot]
  exact arrowhead_zero_center_nonneg t v ht z.ofLp hz

def centerVector : EuclideanSpace ℝ (Option ι) :=
  EuclideanSpace.basisFun (Option ι) ℝ none

def centerMoment (t v : ι → ℝ) (n : ℕ) : ℝ :=
  ⟪centerVector, ((arrowhead t v).toEuclideanLin^n) centerVector⟫

def centerWeight (t v : ι → ℝ) (i : Option ι) : ℝ :=
  ⟪(arrowhead_isHermitian t v).eigenvectorBasis i, centerVector⟫^2

theorem centerMoment_spectral (t v : ι → ℝ) (n : ℕ) :
    centerMoment t v n = ∑ i, centerWeight t v i *
      (arrowhead_isHermitian t v).eigenvalues i^n := by
  exact basis_moment_expansion (arrowhead t v).toEuclideanLin
    (arrowhead_isHermitian t v).eigenvectorBasis
    (arrowhead_isHermitian t v).eigenvalues
    (matrix_eigenvector_action (arrowhead_isHermitian t v)) n centerVector

theorem centerWeight_nonneg (t v : ι → ℝ) (i : Option ι) :
    0 ≤ centerWeight t v i := sq_nonneg _

theorem centerWeight_mass (t v : ι → ℝ) : ∑ i, centerWeight t v i = 1 := by
  simp only [centerWeight]
  rw [(arrowhead_isHermitian t v).eigenvectorBasis.sum_sq_inner_right]
  simp [centerVector]

theorem centerMoment_zero (t v : ι → ℝ) : centerMoment t v 0 = 1 := by
  simp [centerMoment, centerVector]

theorem centerMoment_one (t v : ι → ℝ) : centerMoment t v 1 = 0 := by
  simp [centerMoment, centerVector, Matrix.toLpLin_apply,
    EuclideanSpace.inner_single_left, arrowhead]

theorem centerMoment_two (t v : ι → ℝ) : centerMoment t v 2 = ∑ i, v i^2 := by
  simp only [centerMoment, pow_two, Module.End.mul_apply]
  simp [centerVector, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_option, arrowhead]

theorem centerWeight_mean (t v : ι → ℝ) :
    ∑ i, centerWeight t v i * (arrowhead_isHermitian t v).eigenvalues i = 0 := by
  simpa only [centerMoment_spectral, pow_one] using centerMoment_one t v

theorem centerMoment_increment (t v : ι → ℝ) (n : ℕ) (hn : 0 < n) :
    centerMoment t v n-centerMoment t v (n-1) =
      spectralIncrement (centerWeight t v) (arrowhead_isHermitian t v).eigenvalues n := by
  rw [centerMoment_spectral, centerMoment_spectral, spectralIncrement,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  nth_rw 1 [show n = (n-1)+1 by omega]
  rw [pow_succ]
  ring

end
end FlatBernoulli
