import SpectralCount

/- Classical principal-submatrix and spectral-count tools for the proposed
Kadar–Yu proof. These are supporting lemmas, not a source-conjecture endpoint. -/
namespace KadarYu

open Matrix Finset
open scoped RealInnerProductSpace

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

noncomputable def sumRightLinear : EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ (n ⊕ m) where
  toFun x := WithLp.toLp 2 (Sum.elim (0 : n → ℝ) x.ofLp)
  map_add' x y := by
    apply PiLp.ext
    intro i
    cases i <;> simp
  map_smul' c x := by
    apply PiLp.ext
    intro i
    cases i <;> simp

noncomputable def sumRightIsometry : EuclideanSpace ℝ m →ₗᵢ[ℝ] EuclideanSpace ℝ (n ⊕ m) where
  toLinearMap := sumRightLinear
  norm_map' x := by
    have hsq : ‖sumRightLinear (n := n) x‖ ^ 2 = ‖x‖ ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq]
      simp [sumRightLinear, Fintype.sum_sum_type]
    nlinarith [norm_nonneg (sumRightLinear (n := n) x), norm_nonneg x]

omit [DecidableEq n] [DecidableEq m] in
theorem sumRightIsometry_apply (x : EuclideanSpace ℝ m) :
    (sumRightIsometry (n := n) x).ofLp = Sum.elim (0 : n → ℝ) x.ofLp := rfl

theorem matrix_quadratic_dot (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    ⟪x, A.toEuclideanLin x⟫ = x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, dotProduct_comm]

theorem sumRight_quadratic (A : Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (x : EuclideanSpace ℝ m) :
    ⟪sumRightIsometry (n := n) x, A.toEuclideanLin (sumRightIsometry x)⟫ =
      ⟪x, (A.submatrix Sum.inr Sum.inr).toEuclideanLin x⟫ := by
  rw [matrix_quadratic_dot, matrix_quadratic_dot]
  simp only [sumRightIsometry_apply, dotProduct, mulVec, Fintype.sum_sum_type]
  simp

theorem spectralCountAbove_submatrix_inr
    {A : Matrix (n ⊕ m) (n ⊕ m) ℝ} (hA : A.IsHermitian) (c : ℝ) :
    spectralCountAbove (hA.submatrix Sum.inr) c ≤ spectralCountAbove hA c := by
  apply spectralCountAbove_mono_isometry (hA.submatrix Sum.inr) hA sumRightIsometry c
  intro x
  rw [sumRight_quadratic]

noncomputable def sumLeftProjection : EuclideanSpace ℝ (n ⊕ m) →ₗ[ℝ] (n → ℝ) where
  toFun x i := x (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def sumRightProjection : EuclideanSpace ℝ (n ⊕ m) →ₗ[ℝ] EuclideanSpace ℝ m where
  toFun x := WithLp.toLp 2 (x.ofLp ∘ Sum.inr)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq n] [DecidableEq m] in
theorem sumRight_of_left_zero (x : EuclideanSpace ℝ (n ⊕ m))
    (hx : sumLeftProjection x = 0) : sumRightIsometry (sumRightProjection x) = x := by
  apply PiLp.ext
  intro i
  cases i with
  | inl j => exact (congrFun hx j).symm
  | inr j => rfl

theorem spectralCountAbove_le_head
    {A : Matrix (n ⊕ m) (n ⊕ m) ℝ} (hA : A.IsHermitian) (c : ℝ)
    (htail : ∀ y : EuclideanSpace ℝ m,
      ⟪y, (A.submatrix Sum.inr Sum.inr).toEuclideanLin y⟫ ≤ c * ‖y‖ ^ 2) :
    spectralCountAbove hA c ≤ Fintype.card n := by
  have hker : ∀ x, sumLeftProjection (m := m) x = 0 →
      ⟪x, A.toEuclideanLin x⟫ ≤ c * ‖x‖ ^ 2 := by
    intro x hx
    have he := sumRight_of_left_zero x hx
    calc
      _ = ⟪sumRightIsometry (sumRightProjection x),
        A.toEuclideanLin (sumRightIsometry (sumRightProjection x))⟫ := by rw [he]
      _ = ⟪sumRightProjection x,
        (A.submatrix Sum.inr Sum.inr).toEuclideanLin (sumRightProjection x)⟫ :=
        sumRight_quadratic A _
      _ ≤ c * ‖sumRightProjection x‖ ^ 2 := htail _
      _ = c * ‖x‖ ^ 2 := by
        have hn := (sumRightIsometry (n := n)).norm_map (sumRightProjection x)
        rw [he] at hn
        rw [← hn]
  simpa only [Module.finrank_fintype_fun_eq_card] using
    spectralCountAbove_le_target hA sumLeftProjection c hker

theorem spectralCountAbove_le_head_add_tail
    {A : Matrix (n ⊕ m) (n ⊕ m) ℝ} (hA : A.IsHermitian) (c : ℝ) :
    spectralCountAbove hA c ≤ Fintype.card n +
      spectralCountAbove (hA.submatrix Sum.inr) c := by
  classical
  let hT := hA.submatrix Sum.inr
  let s := univ.filter fun i => c < hT.eigenvalues i
  let R : EuclideanSpace ℝ (n ⊕ m) →ₗ[ℝ] (s → ℝ) :=
    LinearMap.pi fun i =>
      ((innerSL ℝ (hT.eigenvectorBasis i.val)).toLinearMap).comp sumRightProjection
  let L := sumLeftProjection.prod R
  have hker : ∀ x, L x = 0 → ⟪x, A.toEuclideanLin x⟫ ≤ c * ‖x‖ ^ 2 := by
    intro x hx
    have hl : sumLeftProjection x = 0 := congrArg Prod.fst hx
    have hr : R x = 0 := congrArg Prod.snd hx
    have hz : ∀ i, c < hT.eigenvalues i →
        ⟪hT.eigenvectorBasis i, sumRightProjection x⟫ = 0 := by
      intro i hi
      exact congrFun hr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    have he := sumRight_of_left_zero x hl
    calc
      _ = ⟪sumRightIsometry (sumRightProjection x),
        A.toEuclideanLin (sumRightIsometry (sumRightProjection x))⟫ := by rw [he]
      _ = ⟪sumRightProjection x,
        (A.submatrix Sum.inr Sum.inr).toEuclideanLin (sumRightProjection x)⟫ :=
        sumRight_quadratic A _
      _ ≤ c * ‖sumRightProjection x‖ ^ 2 :=
        quadratic_le_of_above_coordinates_zero hT c _ hz
      _ = c * ‖x‖ ^ 2 := by
        have hn := (sumRightIsometry (n := n)).norm_map (sumRightProjection x)
        rw [he] at hn
        rw [← hn]
  have h := spectralCountAbove_le_target hA L c hker
  change spectralCountAbove hA c ≤ Fintype.card n + s.card
  simpa only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] using h

theorem quadratic_le_of_eigenvalues_le {A : Matrix m m ℝ}
    (hA : A.IsHermitian) (c : ℝ) (hbound : ∀ i, hA.eigenvalues i ≤ c)
    (x : EuclideanSpace ℝ m) : ⟪x, A.toEuclideanLin x⟫ ≤ c * ‖x‖ ^ 2 := by
  apply quadratic_le_of_above_coordinates_zero hA c x
  intro i hi
  exact False.elim ((not_lt_of_ge (hbound i)) hi)

theorem unitPath_quadratic_le_two (s : ℕ) (x : EuclideanSpace ℝ (Fin s)) :
    ⟪x, (jacobiMatrix s (fun _ => 0) (fun _ => 1)).toEuclideanLin x⟫ ≤ 2 * ‖x‖ ^ 2 :=
  quadratic_le_of_eigenvalues_le (jacobiMatrix_hermitian s _ _) 2
    (fun i => (unitPath_eigenvalues_in_band s i).2.le) x

theorem spectralCountAbove_two_le_head
    (s : ℕ) {A : Matrix (n ⊕ Fin s) (n ⊕ Fin s) ℝ} (hA : A.IsHermitian)
    (htail : A.submatrix Sum.inr Sum.inr = jacobiMatrix s (fun _ => 0) (fun _ => 1)) :
    spectralCountAbove hA 2 ≤ Fintype.card n := by
  apply spectralCountAbove_le_head hA 2
  intro y
  rw [htail]
  exact unitPath_quadratic_le_two s y

end KadarYu
