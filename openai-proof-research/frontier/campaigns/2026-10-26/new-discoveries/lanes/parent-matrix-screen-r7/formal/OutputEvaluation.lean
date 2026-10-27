import MeanEvaluation

set_option warningAsError true

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace SquaredPolya

def rho : ℝ := (1058821 / 1054721 : ℝ) + 2 * bFactor
def cFactor : ℝ := (Real.sqrt rho)⁻¹
def outputNumerator : Mat2 := gMat + bFactor • fMat
def outputMean : Mat2 := cFactor • outputNumerator

theorem rho_pos : 0 < rho := by
  have hb : 0 ≤ bFactor := Real.sqrt_nonneg _
  dsimp [rho]
  positivity

theorem cFactor_pos : 0 < cFactor := inv_pos.mpr (Real.sqrt_pos.mpr rho_pos)

theorem cFactor_mul_self : cFactor * cFactor = rho⁻¹ := by
  calc
    cFactor * cFactor = (Real.sqrt rho * Real.sqrt rho)⁻¹ := by
      simp only [cFactor, _root_.mul_inv_rev]
    _ = rho⁻¹ := by rw [Real.mul_self_sqrt rho_pos.le]

theorem outputNumerator_posSemidef : outputNumerator.PosSemidef := by
  exact g_posDef.posSemidef.add (f_posDef.posSemidef.smul (Real.sqrt_nonneg _))

theorem outputMean_posSemidef : outputMean.PosSemidef :=
  outputNumerator_posSemidef.smul cFactor_pos.le

theorem outputNumerator_riccati :
    outputNumerator * fMat⁻¹ * outputNumerator = rho • gMat := by
  have hdet : IsUnit fMat.det := fMat.isUnit_iff_isUnit_det.mp f_posDef.isUnit
  have hFJ : fMat * fMat⁻¹ = 1 := Matrix.mul_nonsing_inv fMat hdet
  have hJF : fMat⁻¹ * fMat = 1 := Matrix.nonsing_inv_mul fMat hdet
  calc
    _ = gMat * fMat⁻¹ * gMat + bFactor • (gMat * fMat⁻¹ * fMat) +
        bFactor • (fMat * fMat⁻¹ * gMat) +
        (bFactor * bFactor) • (fMat * fMat⁻¹ * fMat) := by
      simp only [outputNumerator, add_mul, mul_add, smul_mul_assoc,
        mul_smul_comm, smul_add, smul_smul]
      abel
    _ = gMat * fMat⁻¹ * gMat + bFactor • gMat + bFactor • gMat +
        (bFactor * bFactor) • fMat := by
      rw [Matrix.mul_assoc gMat fMat⁻¹ fMat, hJF, hFJ]
      simp
    _ = rho • gMat := by rw [gf_cayley, bFactor_sq]; dsimp [rho]; module

theorem outputMean_riccati : outputMean * fMat⁻¹ * outputMean = gMat := by
  simp only [outputMean, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [outputNumerator_riccati, smul_smul, cFactor_mul_self,
    inv_mul_cancel₀ (ne_of_gt rho_pos), one_smul]

theorem geometricMean_fg : geometricMean fMat gMat = outputMean :=
  geometricMean_eq_of_riccati f_posDef outputMean_posSemidef outputMean_riccati


end SquaredPolya
