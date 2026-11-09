import GradingConsequences
import PolarFrameBridge

set_option autoImplicit false

open Matrix Unitary
open scoped BigOperators ComplexOrder
namespace FourProjection
variable {N I R J S : Type*}
  [Fintype N] [Fintype I] [Fintype R] [Fintype J] [Fintype S]
  [DecidableEq I] [DecidableEq R] [DecidableEq J] [DecidableEq S]

/-- Cancellation uses the strictly positive column spectrum, never an ambient inverse. -/
theorem mpInvSqrt_mul_sqrt_of_posDef {A : Matrix I I ℂ} (hA : A.PosDef) :
    mpInvSqrt A * cfc Real.sqrt A = 1 := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  rw [mpInvSqrt, ← cfc_mul _ _ A (hc _) (hc _), hA.1.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  have hd : diagonal (RCLike.ofReal ∘ (fun t : ℝ => (Real.sqrt t)⁻¹ * Real.sqrt t) ∘
      hA.1.eigenvalues) = (1 : Matrix I I ℂ) := by
    have he (i : I) : (Real.sqrt (hA.1.eigenvalues i))⁻¹ * Real.sqrt (hA.1.eigenvalues i) = 1 :=
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne'
    simp only [Function.comp_def, he, map_one, diagonal_one]
  rw [hd, map_one]

/-- Reconstruct every injective rectangular matrix from its canonical polar frame. -/
theorem polarFrame_mul_sqrt (E : Matrix N I ℂ) (hE : Function.Injective E.mulVec) :
    polarFrame E * cfc Real.sqrt (Eᴴ * E) = E := by
  unfold polarFrame invSqrt
  rw [Matrix.mul_assoc, mpInvSqrt_mul_sqrt_of_posDef (Matrix.PosDef.conjTranspose_mul_self E hE),
    Matrix.mul_one]

/-- The actual cross-Gram matrix is the two-sided square-root reconstruction. -/
theorem crossGram_reconstruction (E : Matrix N I ℂ) (F : Matrix N J ℂ)
    (hE : Function.Injective E.mulVec) (hF : Function.Injective F.mulVec) :
    cfc Real.sqrt (Eᴴ * E) * ((polarFrame E)ᴴ * polarFrame F) *
      cfc Real.sqrt (Fᴴ * F) = Eᴴ * F := by
  have hh : (cfc Real.sqrt (Eᴴ * E)).IsHermitian := (IsSelfAdjoint.cfc).isHermitian
  have he := congrArg Matrix.conjTranspose (polarFrame_mul_sqrt E hE)
  rw [conjTranspose_mul, hh.eq] at he
  calc
    _ = (cfc Real.sqrt (Eᴴ * E) * (polarFrame E)ᴴ) *
        (polarFrame F * cfc Real.sqrt (Fᴴ * F)) := by simp only [Matrix.mul_assoc]
    _ = Eᴴ * F := by rw [he, polarFrame_mul_sqrt F hF]

/-- The fixed sign grading on a direct sum, including empty summands. -/
def frameSign : Matrix (I ⊕ R) (I ⊕ R) ℂ := fromBlocks 1 0 0 (-1)

omit [Fintype I] [Fintype R] in
theorem frameSign_isHermitian : (frameSign (I := I) (R := R)).IsHermitian := by
  show (frameSign)ᴴ = frameSign
  simp [frameSign, fromBlocks_conjTranspose]

theorem frameSign_sq : frameSign (I := I) (R := R) * frameSign = 1 := by
  simp [frameSign, fromBlocks_multiply, fromBlocks_one]

def frameGrading : unitary (Matrix (I ⊕ R) (I ⊕ R) ℂ) :=
  ⟨frameSign, by
    constructor <;> simpa only [star_eq_conjTranspose, frameSign_isHermitian.eq] using
      (frameSign_sq (I := I) (R := R))⟩

omit [Fintype I] [Fintype R] in
/-- The Gram defect is off diagonal when both frames have orthonormal columns. -/
theorem frame_gram_defect (p : Matrix N I ℂ) (r : Matrix N R ℂ)
    (hp : pᴴ * p = 1) (hr : rᴴ * r = 1) :
    (fromCols p r)ᴴ * fromCols p r - 1 = fromBlocks 0 (pᴴ * r) (rᴴ * p) 0 := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, hp, hr,
    ← fromBlocks_one]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem frameSign_offdiag (a : Matrix I R ℂ) (b : Matrix R I ℂ) :
    frameSign * fromBlocks 0 a b 0 * frameSign = -fromBlocks 0 a b 0 := by
  simp only [frameSign, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.neg_mul, Matrix.mul_neg, neg_zero]
  ext (i | i) (j | j) <;> simp

theorem frameSign_gram_anticommute (p : Matrix N I ℂ) (r : Matrix N R ℂ)
    (hp : pᴴ * p = 1) (hr : rᴴ * r = 1) :
    frameSign * ((fromCols p r)ᴴ * fromCols p r - 1) * frameSign =
      -((fromCols p r)ᴴ * fromCols p r - 1) := by
  rw [frame_gram_defect p r hp hr, frameSign_offdiag]

theorem frameSign_cross_odd (p : Matrix N I ℂ) (r : Matrix N R ℂ)
    (q : Matrix N J ℂ) (s : Matrix N S ℂ)
    (hpq : pᴴ * q = 0) (hrs : rᴴ * s = 0) :
    frameSign (I := I) (R := R) * ((fromCols p r)ᴴ * fromCols q s) * frameSign (I := J) (R := S) =
      -((fromCols p r)ᴴ * fromCols q s) := by
  simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, hpq, hrs]
  simp only [frameSign, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.neg_mul, Matrix.mul_neg, neg_zero]
  ext (i | i) (j | j) <;> simp

end FourProjection
