import HSBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace FourProjection
open scoped BigOperators Matrix ComplexConjugate

theorem crossGram_column_bound {N I J : Type*} [Fintype N] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (U : Matrix N I ℂ) (V : Matrix N J ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (j : J) :
    ∑ i, Complex.normSq ((Uᴴ * V) i j) ≤ 1 := by
  let u (i : I) : EuclideanSpace ℂ N := WithLp.toLp 2 (fun n => U n i)
  let v (j : J) : EuclideanSpace ℂ N := WithLp.toLp 2 (fun n => V n j)
  have hu : Orthonormal ℂ u := orthonormal_columns U hU
  have hv : Orthonormal ℂ v := orthonormal_columns V hV
  have hb := hu.sum_inner_products_le (s := Finset.univ) (x := v j)
  have he (i : I) : inner ℂ (u i) (v j) = (Uᴴ * V) i j := by
    simp [u, v, PiLp.inner_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
  simpa only [he, ← Complex.normSq_eq_norm_sq, hv.norm_eq_one j, one_pow] using hb

theorem crossGram_row_bound {N I J : Type*} [Fintype N] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (U : Matrix N I ℂ) (V : Matrix N J ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (i : I) :
    ∑ j, Complex.normSq ((Uᴴ * V) i j) ≤ 1 := by
  have hb := crossGram_column_bound V U hV hU i
  have he : Vᴴ * U = (Uᴴ * V)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [he] at hb
  change (∑ j, Complex.normSq (conj ((Uᴴ * V) i j))) ≤ 1 at hb
  simpa only [Complex.normSq_conj] using hb

theorem isometry_mul_unitary {N I : Type*} [Fintype N] [Fintype I] [DecidableEq I]
    (U : Matrix N I ℂ) (W : Matrix I I ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) :
    (U * W)ᴴ * (U * W) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    _ = Wᴴ * (Uᴴ * U) * W := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, hW]

theorem crossGram_unitary_coordinates {N I J : Type*}
    [Fintype N] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (U : Matrix N I ℂ) (V : Matrix N J ℂ) (W : Matrix I I ℂ) (Z : Matrix J J ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hW : Wᴴ * W = 1) (hZ : Zᴴ * Z = 1) :
    (∀ i, ∑ j, Complex.normSq ((Wᴴ * (Uᴴ * V) * Z) i j) ≤ 1) ∧
    (∀ j, ∑ i, Complex.normSq ((Wᴴ * (Uᴴ * V) * Z) i j) ≤ 1) := by
  have hw := isometry_mul_unitary U W hU hW
  have hz := isometry_mul_unitary V Z hV hZ
  have he : Wᴴ * (Uᴴ * V) * Z = (U*W)ᴴ * (V*Z) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he]
  exact ⟨crossGram_row_bound (U*W) (V*Z) hw hz,
    crossGram_column_bound (U*W) (V*Z) hw hz⟩

end FourProjection
