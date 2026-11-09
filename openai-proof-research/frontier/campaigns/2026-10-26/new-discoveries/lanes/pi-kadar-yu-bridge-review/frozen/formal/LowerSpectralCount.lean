import SumCompression

namespace KadarYu

open Matrix Finset
open scoped RealInnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def spectralCountBelow {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (c : ℝ) : ℕ := by
  classical
  exact (univ.filter fun i => hA.eigenvalues i < c).card

theorem spectralCountBelow_le_target
    {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (L : EuclideanSpace ℝ n →ₗ[ℝ] F) (c : ℝ)
    (hker : ∀ x, L x = 0 → c * ‖x‖ ^ 2 ≤ ⟪x, A.toEuclideanLin x⟫) :
    spectralCountBelow hA c ≤ Module.finrank ℝ F := by
  classical
  let s := univ.filter fun i => hA.eigenvalues i < c
  let u : s → EuclideanSpace ℝ n := fun i => hA.eigenvectorBasis i.val
  have hu : Orthonormal ℝ u :=
    hA.eigenvectorBasis.orthonormal.comp _ Subtype.val_injective
  have he : ∀ i : s, (-A.toEuclideanLin) (u i) = (-hA.eigenvalues i.val) • u i := by
    intro i
    simp only [LinearMap.neg_apply, matrix_eigenbasis_action hA, neg_smul, u]
  have hp : ∀ i : s, -c < -hA.eigenvalues i.val :=
    fun i => neg_lt_neg (mem_filter.mp i.property).2
  have hk : ∀ x, L x = 0 → ⟪x, (-A.toEuclideanLin) x⟫ ≤ -c * ‖x‖ ^ 2 := by
    intro x hx
    simpa only [LinearMap.neg_apply, inner_neg_right, neg_mul] using neg_le_neg (hker x hx)
  have h := positive_eigenfamily_card_le (-A.toEuclideanLin) L u hu
    (fun i : s => -hA.eigenvalues i.val) (-c) he hp hk
  change s.card ≤ Module.finrank ℝ F
  simpa only [Fintype.card_coe] using h

theorem quadratic_ge_of_below_coordinates_zero {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (c : ℝ) (x : EuclideanSpace ℝ n)
    (hz : ∀ i, hA.eigenvalues i < c → ⟪hA.eigenvectorBasis i, x⟫ = 0) :
    c * ‖x‖ ^ 2 ≤ ⟪x, A.toEuclideanLin x⟫ := by
  rw [basis_quadratic_expansion A.toEuclideanLin hA.eigenvectorBasis hA.eigenvalues
    (matrix_eigenbasis_action hA)]
  calc
    _ = ∑ i, c * ⟪hA.eigenvectorBasis i, x⟫ ^ 2 := by
      rw [← mul_sum, hA.eigenvectorBasis.sum_sq_inner_right]
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      by_cases hi : hA.eigenvalues i < c
      · rw [hz i hi]
        simp
      · exact mul_le_mul_of_nonneg_right (le_of_not_gt hi) (sq_nonneg _)

theorem spectralCountBelow_mono_isometry
    {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix m m ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (e : EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ m) (c : ℝ)
    (hform : ∀ x, ⟪e x, B.toEuclideanLin (e x)⟫ ≤ ⟪x, A.toEuclideanLin x⟫) :
    spectralCountBelow hA c ≤ spectralCountBelow hB c := by
  classical
  let s := univ.filter fun i => hB.eigenvalues i < c
  let L : EuclideanSpace ℝ n →ₗ[ℝ] (s → ℝ) :=
    LinearMap.pi fun i => ((innerSL ℝ (hB.eigenvectorBasis i.val)).toLinearMap).comp
      e.toLinearMap
  have hker : ∀ x, L x = 0 → c * ‖x‖ ^ 2 ≤ ⟪x, A.toEuclideanLin x⟫ := by
    intro x hx
    have hz : ∀ i, hB.eigenvalues i < c → ⟪hB.eigenvectorBasis i, e x⟫ = 0 := by
      intro i hi
      exact congrFun hx ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
    calc
      _ = c * ‖e x‖ ^ 2 := by rw [e.norm_map]
      _ ≤ ⟪e x, B.toEuclideanLin (e x)⟫ := quadratic_ge_of_below_coordinates_zero hB c _ hz
      _ ≤ _ := hform x
  have h := spectralCountBelow_le_target hA L c hker
  change spectralCountBelow hA c ≤ s.card
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem spectralCountBelow_submatrix_inr
    {A : Matrix (n ⊕ m) (n ⊕ m) ℝ} (hA : A.IsHermitian) (c : ℝ) :
    spectralCountBelow (hA.submatrix Sum.inr) c ≤ spectralCountBelow hA c := by
  apply spectralCountBelow_mono_isometry (hA.submatrix Sum.inr) hA sumRightIsometry c
  intro x
  rw [sumRight_quadratic]

theorem spectralCountBelow_le_head_add_tail
    {A : Matrix (n ⊕ m) (n ⊕ m) ℝ} (hA : A.IsHermitian) (c : ℝ) :
    spectralCountBelow hA c ≤ Fintype.card n +
      spectralCountBelow (hA.submatrix Sum.inr) c := by
  classical
  let hT := hA.submatrix Sum.inr
  let s := univ.filter fun i => hT.eigenvalues i < c
  let R : EuclideanSpace ℝ (n ⊕ m) →ₗ[ℝ] (s → ℝ) :=
    LinearMap.pi fun i =>
      ((innerSL ℝ (hT.eigenvectorBasis i.val)).toLinearMap).comp sumRightProjection
  let L := sumLeftProjection.prod R
  have hker : ∀ x, L x = 0 → c * ‖x‖ ^ 2 ≤ ⟪x, A.toEuclideanLin x⟫ := by
    intro x hx
    have hl : sumLeftProjection x = 0 := congrArg Prod.fst hx
    have hr : R x = 0 := congrArg Prod.snd hx
    have hz : ∀ i, hT.eigenvalues i < c →
        ⟪hT.eigenvectorBasis i, sumRightProjection x⟫ = 0 := by
      intro i hi
      exact congrFun hr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    have he := sumRight_of_left_zero x hl
    have hn := (sumRightIsometry (n := n)).norm_map (sumRightProjection x)
    rw [he] at hn
    calc
      _ = c * ‖sumRightProjection x‖ ^ 2 := by rw [hn]
      _ ≤ ⟪sumRightProjection x,
        (A.submatrix Sum.inr Sum.inr).toEuclideanLin (sumRightProjection x)⟫ :=
        quadratic_ge_of_below_coordinates_zero hT c _ hz
      _ = ⟪sumRightIsometry (sumRightProjection x),
        A.toEuclideanLin (sumRightIsometry (sumRightProjection x))⟫ :=
        (sumRight_quadratic A _).symm
      _ = _ := by rw [he]
  have h := spectralCountBelow_le_target hA L c hker
  change spectralCountBelow hA c ≤ Fintype.card n + s.card
  simpa only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] using h

theorem quadratic_ge_of_eigenvalues_ge {A : Matrix m m ℝ}
    (hA : A.IsHermitian) (c : ℝ) (hbound : ∀ i, c ≤ hA.eigenvalues i)
    (x : EuclideanSpace ℝ m) : c * ‖x‖ ^ 2 ≤ ⟪x, A.toEuclideanLin x⟫ := by
  apply quadratic_ge_of_below_coordinates_zero hA c x
  intro i hi
  exact False.elim ((not_lt_of_ge (hbound i)) hi)

theorem unitPath_quadratic_ge_neg_two (s : ℕ) (x : EuclideanSpace ℝ (Fin s)) :
    -2 * ‖x‖ ^ 2 ≤ ⟪x, (jacobiMatrix s (fun _ => 0) (fun _ => 1)).toEuclideanLin x⟫ :=
  quadratic_ge_of_eigenvalues_ge (jacobiMatrix_hermitian s _ _) (-2)
    (fun i => (unitPath_eigenvalues_in_band s i).1.le) x

theorem unitPath_spectralCountBelow (s : ℕ) :
    spectralCountBelow (jacobiMatrix_hermitian s (fun _ => 0) (fun _ => 1)) (-2) = 0 := by
  classical
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hl := (unitPath_eigenvalues_in_band s i).1
  exact (not_lt_of_ge hl.le) (mem_filter.mp hi).2

theorem spectralCountBelow_le_head
    {A : Matrix (n ⊕ m) (n ⊕ m) ℝ} (hA : A.IsHermitian) (c : ℝ)
    (htail : ∀ y : EuclideanSpace ℝ m,
      c * ‖y‖ ^ 2 ≤ ⟪y, (A.submatrix Sum.inr Sum.inr).toEuclideanLin y⟫) :
    spectralCountBelow hA c ≤ Fintype.card n := by
  have hker : ∀ x, sumLeftProjection (m := m) x = 0 →
      c * ‖x‖ ^ 2 ≤ ⟪x, A.toEuclideanLin x⟫ := by
    intro x hx
    have he := sumRight_of_left_zero x hx
    have hn := (sumRightIsometry (n := n)).norm_map (sumRightProjection x)
    rw [he] at hn
    calc
      _ = c * ‖sumRightProjection x‖ ^ 2 := by rw [hn]
      _ ≤ ⟪sumRightProjection x,
        (A.submatrix Sum.inr Sum.inr).toEuclideanLin (sumRightProjection x)⟫ := htail _
      _ = ⟪sumRightIsometry (sumRightProjection x),
        A.toEuclideanLin (sumRightIsometry (sumRightProjection x))⟫ :=
        (sumRight_quadratic A _).symm
      _ = _ := by rw [he]
  simpa only [Module.finrank_fintype_fun_eq_card] using
    spectralCountBelow_le_target hA sumLeftProjection c hker

theorem spectralCountBelow_neg_two_le_head
    (s : ℕ) {A : Matrix (n ⊕ Fin s) (n ⊕ Fin s) ℝ} (hA : A.IsHermitian)
    (htail : A.submatrix Sum.inr Sum.inr = jacobiMatrix s (fun _ => 0) (fun _ => 1)) :
    spectralCountBelow hA (-2) ≤ Fintype.card n := by
  apply spectralCountBelow_le_head hA (-2)
  intro y
  rw [htail]
  exact unitPath_quadratic_ge_neg_two s y

end KadarYu
