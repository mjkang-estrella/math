import GeometricMean

set_option warningAsError true

open scoped MatrixOrder ComplexOrder
open Matrix

namespace SquaredPolya

variable {n : Type*} [Fintype n] [DecidableEq n]

def blockDiag (A B : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks A 0 0 B

theorem blockDiag_posSemidef {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (blockDiag A B).PosSemidef := by
  let R := blockDiag (CFC.sqrt A) (CFC.sqrt B)
  have hR : Rᴴ * R = blockDiag A B := by
    simp only [R, blockDiag, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    have hSA0 : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
    have hSB0 : (CFC.sqrt B).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
    have hSA : (CFC.sqrt A)ᴴ = CFC.sqrt A := hSA0.isHermitian
    have hSB : (CFC.sqrt B)ᴴ = CFC.sqrt B := hSB0.isHermitian
    rw [hSA, hSB, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      CFC.sqrt_mul_sqrt_self B hB.nonneg]
  rw [← hR]
  exact Matrix.posSemidef_conjTranspose_mul_self R

theorem blockDiag_posDef {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (blockDiag A B).PosDef := by
  apply (blockDiag_posSemidef hA.posSemidef hB.posSemidef).posDef_iff_isUnit.mpr
  exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA.isUnit, hB.isUnit⟩

noncomputable def blockAverage :
    Matrix (n ⊕ n) (n ⊕ n) ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun Z := (1 / 2 : ℂ) •
    (Z.submatrix Sum.inl Sum.inl + Z.submatrix Sum.inr Sum.inr)
  map_add' Z W := by
    ext i j
    simp [Matrix.submatrix, smul_eq_mul]
    ring
  map_smul' c Z := by
    ext i j
    simp [Matrix.submatrix, smul_eq_mul]
    ring

omit [Fintype n] in
theorem blockAverage_unital : blockAverage (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1 := by
  ext i j
  by_cases h : i = j <;> norm_num [blockAverage, Matrix.one_apply, h]

omit [Fintype n] [DecidableEq n] in
theorem blockAverage_positive {Z : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hZ : Z.PosSemidef) : (blockAverage Z).PosSemidef := by
  exact ((hZ.submatrix Sum.inl).add (hZ.submatrix Sum.inr)).smul
    (by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im] : (0 : ℂ) ≤ 1 / 2)

omit [Fintype n] [DecidableEq n] in
theorem blockAverage_blockDiag (A B : Matrix n n ℂ) :
    blockAverage (blockDiag A B) = (1 / 2 : ℂ) • (A + B) := by
  ext i j
  rfl


end SquaredPolya
