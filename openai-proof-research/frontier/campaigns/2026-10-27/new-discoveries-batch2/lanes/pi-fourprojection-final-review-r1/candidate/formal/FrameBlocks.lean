import FrameReconstruction

set_option autoImplicit false

open Matrix Unitary
open scoped BigOperators ComplexOrder
namespace FourProjection
variable {N I R J S : Type*}
  [Fintype N] [Fintype I] [Fintype R] [Fintype J] [Fintype S]
  [DecidableEq N] [DecidableEq I] [DecidableEq R] [DecidableEq J] [DecidableEq S]

omit [DecidableEq I] [DecidableEq R] [DecidableEq J] [DecidableEq S] in
theorem hsSq_fromBlocks (a : Matrix I J ℂ) (b : Matrix I S ℂ)
    (c : Matrix R J ℂ) (d : Matrix R S ℂ) :
    hsSq (fromBlocks a b c d) = hsSq a + hsSq b + hsSq c + hsSq d := by
  simp only [hsSq, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

omit [DecidableEq I] [DecidableEq J] in
theorem hsSq_zero : hsSq (0 : Matrix I J ℂ) = 0 := by simp [hsSq]

omit [DecidableEq I] [DecidableEq J] in
theorem hsSq_double (a : Matrix I J ℂ) : hsSq (a + a) = 4 * hsSq a := by
  have he (z : ℂ) : Complex.normSq (z + z) = 4 * Complex.normSq z := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    ring
  simp only [hsSq, Matrix.add_apply, he, Finset.mul_sum]

theorem frameSign_pinching (K : Matrix (I ⊕ R) (J ⊕ S) ℂ) :
    hsSq (K + frameSign (I := I) (R := R) * K * frameSign (I := J) (R := S)) / 4 = hsSq K.toBlocks₁₁ + hsSq K.toBlocks₂₂ := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, K = fromBlocks a b c d :=
    ⟨_, _, _, _, K.fromBlocks_toBlocks.symm⟩
  have he : fromBlocks a b c d + frameSign (I := I) (R := R) * fromBlocks a b c d * frameSign (I := J) (R := S) =
      fromBlocks (a+a) 0 0 (d+d) := by
    simp only [frameSign, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    ext (i | i) (j | j) <;> simp
  rw [he, hsSq_fromBlocks, hsSq_zero, hsSq_zero, hsSq_double, hsSq_double]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]
  ring

omit [DecidableEq I] [DecidableEq R] in
theorem trace_fromBlocks (a : Matrix I I ℂ) (b : Matrix I R ℂ)
    (c : Matrix R I ℂ) (d : Matrix R R ℂ) :
    trace (fromBlocks a b c d) = trace a + trace d := by
  simp [trace, diag, Fintype.sum_sum_type]

omit [DecidableEq N] in
/-- The Gram-defect energy equals twice the original overlap trace. -/
theorem frame_gram_energy (p : Matrix N I ℂ) (r : Matrix N R ℂ)
    (hp : pᴴ * p = 1) (hr : rᴴ * r = 1) :
    (trace (((fromCols p r)ᴴ * fromCols p r - 1) *
      ((fromCols p r)ᴴ * fromCols p r - 1))).re =
      2 * (trace ((p * pᴴ) * (r * rᴴ))).re := by
  rw [frame_gram_defect p r hp hr]
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    trace_fromBlocks, Complex.add_re]
  have hadj : rᴴ * p = (pᴴ * r)ᴴ := by simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [hadj, trace_mul_conjTranspose_self_re, trace_conjTranspose_mul_self_re,
    trace_frame_products]
  ring

omit [Fintype N] [DecidableEq N] [DecidableEq I] [DecidableEq R] in
/-- The ambient Gram matrix is exactly the sum of the two original frame projections. -/
theorem fromCols_mul_adjoint (p : Matrix N I ℂ) (r : Matrix N R ℂ) :
    fromCols p r * (fromCols p r)ᴴ = p * pᴴ + r * rᴴ := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]

/-- Literal normalization of the first frame of a pair. -/
noncomputable def normalizedFrame (p : Matrix N I ℂ) (r : Matrix N R ℂ) : Matrix N I ℂ :=
  mpInvSqrt (p * pᴴ + r * rᴴ) * p

theorem polarFrame_fromCols (p : Matrix N I ℂ) (r : Matrix N R ℂ) :
    polarFrame (fromCols p r) = fromCols (normalizedFrame p r) (normalizedFrame r p) := by
  rw [polarFrame_eq_mpInvSqrt_mul, fromCols_mul_adjoint, mul_fromCols]
  simp only [normalizedFrame, add_comm (r * rᴴ) (p * pᴴ)]

omit [DecidableEq I] [DecidableEq R] in
/-- Each literal Moore–Penrose congruence is the projection of its normalized frame. -/
theorem normalizedFrame_projection (p : Matrix N I ℂ) (r : Matrix N R ℂ) :
    mpInvSqrt (p * pᴴ + r * rᴴ) * (p * pᴴ) * mpInvSqrt (p * pᴴ + r * rᴴ) =
      normalizedFrame p r * (normalizedFrame p r)ᴴ := by
  simp only [normalizedFrame, conjTranspose_mul, (mpInvSqrt_isHermitian _).eq, Matrix.mul_assoc]

/-- The diagonal-block HS energy is the literal normalized projection target. -/
theorem normalized_target_energy (p : Matrix N I ℂ) (r : Matrix N R ℂ)
    (q : Matrix N J ℂ) (s : Matrix N S ℂ) :
    let U := polarFrame (fromCols p r)
    let V := polarFrame (fromCols q s)
    hsSq (Uᴴ * V + frameSign (I := I) (R := R) * (Uᴴ * V) * frameSign (I := J) (R := S)) / 4 =
      (trace ((mpInvSqrt (p*pᴴ+r*rᴴ) * (p*pᴴ) * mpInvSqrt (p*pᴴ+r*rᴴ)) *
              (mpInvSqrt (q*qᴴ+s*sᴴ) * (q*qᴴ) * mpInvSqrt (q*qᴴ+s*sᴴ))) +
       trace ((mpInvSqrt (p*pᴴ+r*rᴴ) * (r*rᴴ) * mpInvSqrt (p*pᴴ+r*rᴴ)) *
              (mpInvSqrt (q*qᴴ+s*sᴴ) * (s*sᴴ) * mpInvSqrt (q*qᴴ+s*sᴴ)))).re := by
  dsimp only
  rw [frameSign_pinching, polarFrame_fromCols, polarFrame_fromCols,
    conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂, Complex.add_re]
  rw [normalizedFrame_projection p r, normalizedFrame_projection q s]
  have hr : mpInvSqrt (p*pᴴ+r*rᴴ) * (r*rᴴ) * mpInvSqrt (p*pᴴ+r*rᴴ) =
      normalizedFrame r p * (normalizedFrame r p)ᴴ := by
    simpa only [add_comm (r*rᴴ) (p*pᴴ)] using normalizedFrame_projection r p
  have hs : mpInvSqrt (q*qᴴ+s*sᴴ) * (s*sᴴ) * mpInvSqrt (q*qᴴ+s*sᴴ) =
      normalizedFrame s q * (normalizedFrame s q)ᴴ := by
    simpa only [add_comm (s*sᴴ) (q*qᴴ)] using normalizedFrame_projection s q
  rw [hr, hs, trace_frame_products, trace_frame_products]

end FourProjection
