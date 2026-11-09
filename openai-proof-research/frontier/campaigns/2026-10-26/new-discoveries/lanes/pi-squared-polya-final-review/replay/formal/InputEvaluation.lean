import MeanEvaluation

set_option warningAsError true

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace SquaredPolya

abbrev Mat4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ

def inputU : Mat4 := blockDiag aMat bMat
def inputV : Mat4 := blockDiag bMat 1
def inputMean : Mat4 := blockDiag abMean tMat

theorem blockAverage_blockDiag_real (X Y : Mat2) :
    blockAverage (blockDiag X Y) = (1 / 2 : ℝ) • (X + Y) := by
  rw [blockAverage_blockDiag]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Complex.real_smul, smul_eq_mul]
  norm_num

theorem inputU_posDef : inputU.PosDef := blockDiag_posDef a_posDef b_posDef
theorem inputV_posDef : inputV.PosDef := blockDiag_posDef b_posDef Matrix.PosDef.one

theorem inputU_inv : inputU⁻¹ = blockDiag aMat⁻¹ bMat⁻¹ := by
  apply Matrix.inv_eq_right_inv
  have hA := aMat.isUnit_iff_isUnit_det.mp a_posDef.isUnit
  have hB := bMat.isUnit_iff_isUnit_det.mp b_posDef.isUnit
  simp [inputU, blockDiag, Matrix.fromBlocks_multiply,
    Matrix.mul_nonsing_inv aMat hA, Matrix.mul_nonsing_inv bMat hB]

theorem inputMean_posSemidef : inputMean.PosSemidef :=
  blockDiag_posSemidef abMean_posSemidef t_posSemidef

theorem inputMean_riccati : inputMean * inputU⁻¹ * inputMean = inputV := by
  rw [inputU_inv]
  simp [inputMean, inputV, blockDiag, Matrix.fromBlocks_multiply,
    abMean_riccati, t_riccati]

theorem geometricMean_inputs : geometricMean inputU inputV = inputMean :=
  geometricMean_eq_of_riccati inputU_posDef inputMean_posSemidef inputMean_riccati

theorem inputU_image : blockAverage inputU = fMat := by
  rw [inputU, blockAverage_blockDiag_real, ← f_eq]

theorem inputV_image : blockAverage inputV = gMat := by
  rw [inputV, blockAverage_blockDiag_real, ← g_eq]

theorem inputMean_image : blockAverage (geometricMean inputU inputV) =
    aFactor • fMat + (1 / 2 : ℝ) • tMat := by
  rw [geometricMean_inputs, inputMean, blockAverage_blockDiag_real, abMean, f_eq]
  module

theorem blockDiag_lower {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : (A - 1).PosSemidef) (hB : (B - 1).PosSemidef) :
    (blockDiag A B - 1).PosSemidef := by
  have heq : blockDiag A B - 1 = blockDiag (A - 1) (B - 1) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [blockDiag, Matrix.one_apply]
  rw [heq]
  exact blockDiag_posSemidef hA hB

theorem blockDiag_upper {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} {r : ℝ}
    (hA : (r • (1 : Matrix n n ℂ) - A).PosSemidef)
    (hB : (r • (1 : Matrix n n ℂ) - B).PosSemidef) :
    (r • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) - blockDiag A B).PosSemidef := by
  have heq : r • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) - blockDiag A B =
      blockDiag (r • (1 : Matrix n n ℂ) - A) (r • (1 : Matrix n n ℂ) - B) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [blockDiag, Matrix.one_apply]
  rw [heq]
  exact blockDiag_posSemidef hA hB

theorem inputU_lower : (inputU - 1).PosSemidef := blockDiag_lower a_lower b_lower
theorem inputU_upper : ((1024 : ℝ) • (1 : Mat4) - inputU).PosSemidef :=
  blockDiag_upper a_upper b_upper
theorem inputV_lower : (inputV - 1).PosSemidef := by
  apply blockDiag_lower b_lower
  simpa using (Matrix.PosSemidef.zero : (0 : Mat2).PosSemidef)
theorem inputV_upper : ((1024 : ℝ) • (1 : Mat4) - inputV).PosSemidef := by
  apply blockDiag_upper b_upper
  have heq : (1024 : ℝ) • (1 : Mat2) - 1 = (1023 : ℝ) • (1 : Mat2) := by module
  rw [heq]
  exact Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1023)


end SquaredPolya
