import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace FourProjection
open scoped BigOperators ComplexConjugate Matrix

def hsSq {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I J ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

theorem hsSq_nonneg {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I J ℂ) :
    0 ≤ hsSq M := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem hsSq_conjTranspose {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) : hsSq Mᴴ = hsSq M := by
  change (∑ j, ∑ i, Complex.normSq (conj (M i j))) = ∑ i, ∑ j, Complex.normSq (M i j)
  simp only [Complex.normSq_conj]
  exact Finset.sum_comm

theorem trace_conjTranspose_mul_self_re {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) : (Matrix.trace (Mᴴ * M)).re = hsSq M := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  simp [hsSq, Complex.mul_re, Complex.normSq_apply]

theorem trace_mul_conjTranspose_self_re {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) : (Matrix.trace (M * Mᴴ)).re = hsSq M := by
  rw [Matrix.trace_mul_comm, trace_conjTranspose_mul_self_re]

theorem hsSq_isometry_mul {N I J : Type*} [Fintype N] [Fintype I] [Fintype J]
    [DecidableEq I] (U : Matrix N I ℂ) (M : Matrix I J ℂ) (hU : Uᴴ * U = 1) :
    hsSq (U * M) = hsSq M := by
  rw [← trace_conjTranspose_mul_self_re, Matrix.conjTranspose_mul]
  have he : (Mᴴ * Uᴴ) * (U * M) = Mᴴ * M := by
    calc
      _ = Mᴴ * (Uᴴ * U) * M := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]
  rw [he, trace_conjTranspose_mul_self_re]

theorem hsSq_mul_coisometry {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq J] (M : Matrix I J ℂ) (V : Matrix J N ℂ) (hV : V * Vᴴ = 1) :
    hsSq (M * V) = hsSq M := by
  rw [← hsSq_conjTranspose (M * V), Matrix.conjTranspose_mul]
  have hh : (Vᴴ)ᴴ * Vᴴ = 1 := by simpa only [Matrix.conjTranspose_conjTranspose] using hV
  rw [hsSq_isometry_mul Vᴴ Mᴴ hh, hsSq_conjTranspose]

theorem trace_frame_products {N I J : Type*} [Fintype N] [Fintype I] [Fintype J]
    (p : Matrix N I ℂ) (q : Matrix N J ℂ) :
    (Matrix.trace ((p * pᴴ) * (q * qᴴ))).re = hsSq (pᴴ * q) := by
  have he : pᴴ * (q*qᴴ) * p = (pᴴ*q) * (pᴴ*q)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm p (pᴴ*(q*qᴴ)), he,
    trace_mul_conjTranspose_self_re]

theorem orthonormal_columns {N I : Type*} [Fintype N] [Fintype I] [DecidableEq I]
    (U : Matrix N I ℂ) (hU : Uᴴ * U = 1) :
    Orthonormal ℂ (fun i => (WithLp.toLp 2 (fun n => U n i) : EuclideanSpace ℂ N)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have he := congrFun (congrFun hU i) j
  simpa [PiLp.inner_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_comm] using he

end FourProjection
