import GradedSpectralBridge
open Matrix Unitary
open scoped BigOperators ComplexOrder
namespace FourProjection
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Positive definiteness of both shifts gives strict bounds on the actual spectrum. -/
theorem spectrum_bounds_of_posDef_shifts {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (hplus : (1 + A).PosDef) (hminus : (1 - A).PosDef) :
    ∀ t ∈ spectrum ℝ A, -1 < t ∧ t < 1 := by
  let P : Matrix I I ℂ := hA.eigenvectorUnitary
  let D : Matrix I I ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hp : star P * P = 1 := coe_star_mul_self hA.eigenvectorUnitary
  have ha : A = P * D * star P := hA.spectral_theorem
  have hinj : Function.Injective P.mulVec :=
    Matrix.mulVec_injective_of_isUnit (show IsUnit P from Unitary.isUnit_coe)
  have hep : Pᴴ * (1 + A) * P = diagonal (fun i => ((1 + hA.eigenvalues i : ℝ) : ℂ)) := by
    conv_lhs => rw [ha]
    simp only [← star_eq_conjTranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.mul_assoc, ← Matrix.mul_assoc (star P) P, hp, Matrix.one_mul, Matrix.mul_one]
    simp [D, Complex.ofReal_add, ← diagonal_one, ← diagonal_add]
  have hem : Pᴴ * (1 - A) * P = diagonal (fun i => ((1 - hA.eigenvalues i : ℝ) : ℂ)) := by
    conv_lhs => rw [ha]
    simp only [← star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_assoc, ← Matrix.mul_assoc (star P) P, hp, Matrix.one_mul, Matrix.mul_one]
    simp [D, Complex.ofReal_sub, ← diagonal_one, ← diagonal_sub]
  have hdp := hplus.conjTranspose_mul_mul_same hinj
  have hdm := hminus.conjTranspose_mul_mul_same hinj
  rw [hep, posDef_diagonal_iff] at hdp
  rw [hem, posDef_diagonal_iff] at hdm
  intro t ht
  rw [hA.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  have hl : 0 < (1 + hA.eigenvalues i : ℝ) := by exact_mod_cast hdp i
  have hu : 0 < (1 - hA.eigenvalues i : ℝ) := by exact_mod_cast hdm i
  constructor <;> linarith

/-- A self-adjoint unitary grading transports positivity of the positive shift. -/
theorem posDef_one_sub_of_grading {A : Matrix I I ℂ}
    (hplus : (1 + A).PosDef) (G : unitary (Matrix I I ℂ))
    (hG : (G : Matrix I I ℂ).IsHermitian)
    (hanti : (G : Matrix I I ℂ) * A * (G : Matrix I I ℂ) = -A) :
    (1 - A).PosDef := by
  have he : (G : Matrix I I ℂ)ᴴ * (1 + A) * (G : Matrix I I ℂ) = 1 - A := by
    rw [hG.eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hanti]
    have hgg : (G : Matrix I I ℂ) * (G : Matrix I I ℂ) = 1 := by
      simpa only [star_eq_conjTranspose, hG.eq] using coe_star_mul_self G
    rw [hgg, sub_eq_add_neg]
  rw [← he]
  exact hplus.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit Unitary.isUnit_coe)

/-- The off-diagonal/odd cross-Gram identity implies the genuine two-root equation. -/
theorem sqrt_relation_of_odd_cross {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (G : Matrix I I ℂ) (H : Matrix J J ℂ)
    (hG : G * G = 1) (hH : H * H = 1)
    (ha : G * A * G = -A) (hb : H * B * H = -B)
    (K : Matrix I J ℂ)
    (hodd : G * (cfc Real.sqrt (1 + A) * K * cfc Real.sqrt (1 + B)) * H =
      -(cfc Real.sqrt (1 + A) * K * cfc Real.sqrt (1 + B))) :
    cfc Real.sqrt (1 + A) * K * cfc Real.sqrt (1 + B) +
      cfc Real.sqrt (1 - A) * (G * K * H) * cfc Real.sqrt (1 - B) = 0 := by
  rw [← sqrt_grading hA G hG ha, ← sqrt_grading hB H hH hb]
  have he : (G * cfc Real.sqrt (1 + A) * G) * (G * K * H) *
      (H * cfc Real.sqrt (1 + B) * H) =
      G * (cfc Real.sqrt (1 + A) * K * cfc Real.sqrt (1 + B)) * H := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc G G, hG, Matrix.one_mul,
      ← Matrix.mul_assoc H H, hH]
  rw [he, hodd, add_neg_cancel]
/-- Complete graded spectral bridge for cross-Gram matrices of isometries.
The parent must construct these frames and identify the odd cross-Gram equation. -/
theorem graded_cross_isometry_bound {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hplusA : (1 + A).PosDef) (hplusB : (1 + B).PosDef)
    (G : unitary (Matrix I I ℂ)) (H : unitary (Matrix J J ℂ))
    (hG : (G : Matrix I I ℂ).IsHermitian) (hH : (H : Matrix J J ℂ).IsHermitian)
    (ha : (G : Matrix I I ℂ) * A * (G : Matrix I I ℂ) = -A)
    (hb : (H : Matrix J J ℂ) * B * (H : Matrix J J ℂ) = -B)
    (U : Matrix N I ℂ) (V : Matrix N J ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hodd : (G : Matrix I I ℂ) *
        (cfc Real.sqrt (1 + A) * (Uᴴ * V) * cfc Real.sqrt (1 + B)) * (H : Matrix J J ℂ) =
      -(cfc Real.sqrt (1 + A) * (Uᴴ * V) * cfc Real.sqrt (1 + B))) :
    hsSq ((Uᴴ * V) + (G : Matrix I I ℂ) * (Uᴴ * V) * (H : Matrix J J ℂ)) / 4 ≤
      (trace (A * A) + trace (B * B)).re / 2 := by
  have hgg : (G : Matrix I I ℂ) * (G : Matrix I I ℂ) = 1 := by
    simpa only [star_eq_conjTranspose, hG.eq] using coe_star_mul_self G
  have hhh : (H : Matrix J J ℂ) * (H : Matrix J J ℂ) = 1 := by
    simpa only [star_eq_conjTranspose, hH.eq] using coe_star_mul_self H
  apply graded_spectral_bound hA hB
    (spectrum_bounds_of_posDef_shifts hA hplusA (posDef_one_sub_of_grading hplusA G hG ha))
    (spectrum_bounds_of_posDef_shifts hB hplusB (posDef_one_sub_of_grading hplusB H hH hb))
    G H (Uᴴ * V) (gramContractive_cross_isometries U V hU hV)
  exact sqrt_relation_of_odd_cross hA hB G H hgg hhh ha hb (Uᴴ * V) hodd

end FourProjection
