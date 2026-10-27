import LowerSpectralCount

namespace KadarYu

open Matrix Finset
open scoped RealInnerProductSpace

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

noncomputable def principalLinear (f : n ↪ m) :
    EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ m where
  toFun x := ∑ i, x i • (EuclideanSpace.basisFun m ℝ) (f i)
  map_add' x y := by
    simp only [PiLp.add_apply, add_smul, sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, smul_sum, RingHom.id_apply]

noncomputable def principalIsometry (f : n ↪ m) :
    EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ m where
  toLinearMap := principalLinear f
  norm_map' x := by
    have hON := (EuclideanSpace.basisFun m ℝ).orthonormal.comp f f.injective
    have hs := orthonormal_combination_norm_sq
      (fun i => (EuclideanSpace.basisFun m ℝ) (f i)) hON (fun i => x i)
    change ‖∑ i, x i • (EuclideanSpace.basisFun m ℝ) (f i)‖ = ‖x‖
    rw [← EuclideanSpace.real_norm_sq_eq] at hs
    nlinarith [norm_nonneg (∑ i, x i • (EuclideanSpace.basisFun m ℝ) (f i)), norm_nonneg x]

omit [DecidableEq n] [DecidableEq m] in
theorem principalIsometry_apply (f : n ↪ m) (x : EuclideanSpace ℝ n) :
    principalIsometry f x = ∑ i, x i • (EuclideanSpace.basisFun m ℝ) (f i) := rfl

theorem basisFun_matrix_entry (B : Matrix m m ℝ) (i j : m) :
    ⟪(EuclideanSpace.basisFun m ℝ) i,
      B.toEuclideanLin ((EuclideanSpace.basisFun m ℝ) j)⟫ = B i j := by
  rw [EuclideanSpace.basisFun_inner]
  simp [EuclideanSpace.basisFun_apply, Matrix.toLpLin_apply]

theorem principalIsometry_quadratic (f : n ↪ m) (B : Matrix m m ℝ)
    (x : EuclideanSpace ℝ n) :
    ⟪principalIsometry f x, B.toEuclideanLin (principalIsometry f x)⟫ =
      ⟪x, (B.submatrix f f).toEuclideanLin x⟫ := by
  rw [principalIsometry_apply, map_sum]
  simp only [map_smul, inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right,
    basisFun_matrix_entry]
  rw [matrix_quadratic_dot]
  simp only [dotProduct, mulVec, Matrix.submatrix_apply]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  ring

theorem spectralCountAbove_principal (f : n ↪ m) {B : Matrix m m ℝ}
    (hB : B.IsHermitian) (c : ℝ) :
    spectralCountAbove (hB.submatrix f) c ≤ spectralCountAbove hB c := by
  apply spectralCountAbove_mono_isometry (hB.submatrix f) hB (principalIsometry f) c
  intro x
  rw [principalIsometry_quadratic]

theorem spectralCountBelow_principal (f : n ↪ m) {B : Matrix m m ℝ}
    (hB : B.IsHermitian) (c : ℝ) :
    spectralCountBelow (hB.submatrix f) c ≤ spectralCountBelow hB c := by
  apply spectralCountBelow_mono_isometry (hB.submatrix f) hB (principalIsometry f) c
  intro x
  rw [principalIsometry_quadratic]

omit [Fintype m] [DecidableEq m] in
theorem spectralCountAbove_congr {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (he : A = B) (c : ℝ) :
    spectralCountAbove hA c = spectralCountAbove hB c := by
  subst B
  rfl

omit [Fintype m] [DecidableEq m] in
theorem spectralCountBelow_congr {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (he : A = B) (c : ℝ) :
    spectralCountBelow hA c = spectralCountBelow hB c := by
  subst B
  rfl

theorem spectralCountAbove_submatrix_equiv (e : n ≃ m) {B : Matrix m m ℝ}
    (hB : B.IsHermitian) (c : ℝ) :
    spectralCountAbove (hB.submatrix e) c = spectralCountAbove hB c := by
  apply Nat.le_antisymm (spectralCountAbove_principal e.toEmbedding hB c)
  have h := spectralCountAbove_principal e.symm.toEmbedding (hB.submatrix e) c
  have hm : (B.submatrix e e).submatrix e.symm e.symm = B := by
    apply Matrix.ext
    intro i j
    simp
  exact (spectralCountAbove_congr _ hB hm c).symm.trans_le h

theorem spectralCountBelow_submatrix_equiv (e : n ≃ m) {B : Matrix m m ℝ}
    (hB : B.IsHermitian) (c : ℝ) :
    spectralCountBelow (hB.submatrix e) c = spectralCountBelow hB c := by
  apply Nat.le_antisymm (spectralCountBelow_principal e.toEmbedding hB c)
  have h := spectralCountBelow_principal e.symm.toEmbedding (hB.submatrix e) c
  have hm : (B.submatrix e e).submatrix e.symm e.symm = B := by
    apply Matrix.ext
    intro i j
    simp
  exact (spectralCountBelow_congr _ hB hm c).symm.trans_le h

end KadarYu
