import HSBridge
open Matrix Unitary
open scoped BigOperators ComplexOrder
namespace FourProjection
variable {N I J : Type*} [Fintype N] [Fintype I] [Fintype J]
  [DecidableEq N] [DecidableEq I] [DecidableEq J]

/-- Both rectangular Gram complements are positive semidefinite. -/
def GramContractive (K : Matrix I J ℂ) : Prop :=
  (1 - K * Kᴴ).PosSemidef ∧ (1 - Kᴴ * K).PosSemidef

 theorem row_bound_of_gramContractive {K : Matrix I J ℂ} (hK : GramContractive K) (i : I) :
    ∑ j, Complex.normSq (K i j) ≤ 1 := by
  have h := hK.1.diag_nonneg (i := i)
  have hr : 0 ≤ ((1 - K * Kᴴ : Matrix I I ℂ) i i).re := h.1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re,
    Matrix.mul_apply, Matrix.conjTranspose_apply] at hr
  simpa [Complex.normSq_apply, sub_eq_add_neg] using (sub_nonneg.mp hr)

 theorem col_bound_of_gramContractive {K : Matrix I J ℂ} (hK : GramContractive K) (j : J) :
    ∑ i, Complex.normSq (K i j) ≤ 1 := by
  have ht : GramContractive Kᴴ := by
    simpa only [GramContractive, Matrix.conjTranspose_conjTranspose] using And.symm hK
  simpa only [Matrix.conjTranspose_apply, RCLike.star_def, Complex.normSq_conj] using
    row_bound_of_gramContractive ht j

/-- Gram contractivity is preserved under independent unitary basis changes. -/
theorem GramContractive.unitary_change {K : Matrix I J ℂ} (hK : GramContractive K)
    (P : unitary (Matrix I I ℂ)) (Q : unitary (Matrix J J ℂ)) :
    GramContractive (star (P : Matrix I I ℂ) * K * (Q : Matrix J J ℂ)) := by
  have hp : star (P : Matrix I I ℂ) * (P : Matrix I I ℂ) = 1 := coe_star_mul_self P
  have hp' : (P : Matrix I I ℂ) * star (P : Matrix I I ℂ) = 1 := coe_mul_star_self P
  have hq : star (Q : Matrix J J ℂ) * (Q : Matrix J J ℂ) = 1 := coe_star_mul_self Q
  have hq' : (Q : Matrix J J ℂ) * star (Q : Matrix J J ℂ) = 1 := coe_mul_star_self Q
  have he1 : 1 - (star (P : Matrix I I ℂ) * K * (Q : Matrix J J ℂ)) *
      (star (P : Matrix I I ℂ) * K * (Q : Matrix J J ℂ))ᴴ =
      star (P : Matrix I I ℂ) * (1 - K * Kᴴ) * (P : Matrix I I ℂ) := by
    simp only [Matrix.conjTranspose_mul, ← star_eq_conjTranspose, star_star, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hp, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Q : Matrix J J ℂ) (star (Q : Matrix J J ℂ)), hq', Matrix.one_mul]
  have he2 : 1 - (star (P : Matrix I I ℂ) * K * (Q : Matrix J J ℂ))ᴴ *
      (star (P : Matrix I I ℂ) * K * (Q : Matrix J J ℂ)) =
      star (Q : Matrix J J ℂ) * (1 - Kᴴ * K) * (Q : Matrix J J ℂ) := by
    simp only [Matrix.conjTranspose_mul, ← star_eq_conjTranspose, star_star, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hq, Matrix.mul_assoc,
      ← Matrix.mul_assoc (P : Matrix I I ℂ) (star (P : Matrix I I ℂ)), hp', Matrix.one_mul]
  constructor
  · rw [he1]
    exact hK.1.conjTranspose_mul_mul_same (P : Matrix I I ℂ)
  · rw [he2]
    exact hK.2.conjTranspose_mul_mul_same (Q : Matrix J J ℂ)

/-- The orthogonal-complement Gram matrix of an isometry is positive semidefinite. -/
theorem isometry_complement_posSemidef (U : Matrix N I ℂ) (hU : Uᴴ * U = 1) :
    (1 - U * Uᴴ).PosSemidef := by
  have he : (1 - U * Uᴴ) * (1 - U * Uᴴ)ᴴ = 1 - U * Uᴴ := by
    have hproj : (U * Uᴴ) * (U * Uᴴ) = U * Uᴴ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hproj]
    abel
  rw [← he]
  exact posSemidef_self_mul_conjTranspose _

/-- Cross-Gram matrices of arbitrary rectangular isometries satisfy both contractions. -/
theorem gramContractive_cross_isometries (U : Matrix N I ℂ) (V : Matrix N J ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) : GramContractive (Uᴴ * V) := by
  have hu := (isometry_complement_posSemidef U hU).conjTranspose_mul_mul_same V
  have hv := (isometry_complement_posSemidef V hV).conjTranspose_mul_mul_same U
  constructor
  · convert hv using 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU, Matrix.mul_assoc]
  · convert hu using 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV, Matrix.mul_assoc]
end FourProjection
