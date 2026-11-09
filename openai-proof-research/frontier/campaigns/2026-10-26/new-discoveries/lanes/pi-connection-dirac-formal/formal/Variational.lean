import TopSums

/- Classical finite-dimensional Ky Fan variational inequality. This is proof
infrastructure; it is not claimed as a new mathematical result. -/

open Finset Matrix
open scoped RealInnerProductSpace

namespace ConnectionGraph

variable {α β E : Type*} [Fintype α] [Fintype β]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem basis_quadratic_expansion (T : E →ₗ[ℝ] E)
    (b : OrthonormalBasis α ℝ E) (μ : α → ℝ)
    (he : ∀ i, T (b i) = μ i • b i) (x : E) :
    ⟪x, T x⟫ = ∑ i, μ i * ⟪b i, x⟫ ^ 2 := by
  have hT : T x = ∑ i, ⟪b i, x⟫ • (μ i • b i) := by
    nth_rw 1 [← b.sum_repr' x]
    simp only [map_sum, map_smul, he]
  rw [hT, inner_sum]
  apply sum_congr rfl
  intro i _
  simp only [real_inner_smul_right, real_inner_comm x (b i)]
  ring

theorem orthonormal_basis_weights (b : OrthonormalBasis α ℝ E)
    (u : β → E) (hu : Orthonormal ℝ u) :
    (∀ j, 0 ≤ (∑ i, ⟪b j, u i⟫ ^ 2) ∧ (∑ i, ⟪b j, u i⟫ ^ 2) ≤ 1) ∧
      (∑ j, ∑ i, ⟪b j, u i⟫ ^ 2) = Fintype.card β := by
  constructor
  · intro j
    constructor
    · exact sum_nonneg fun _ _ => sq_nonneg _
    · have h := hu.sum_inner_products_le (s := univ) (b j)
      simpa only [real_inner_comm (u _) (b j), Real.norm_eq_abs, sq_abs,
        b.orthonormal.norm_eq_one j, one_pow] using h
  · rw [sum_comm]
    simp_rw [b.sum_sq_inner_right, hu.norm_eq_one, one_pow]
    simp

theorem orthonormal_trace_le [DecidableEq α] (T : E →ₗ[ℝ] E)
    (b : OrthonormalBasis α ℝ E) (μ : α → ℝ)
    (he : ∀ i, T (b i) = μ i • b i)
    (u : β → E) (hu : Orthonormal ℝ u)
    (hk : Fintype.card β ≤ Fintype.card α) :
    (∑ i, ⟪u i, T (u i)⟫) ≤ sortedTopSum μ (Fintype.card β) := by
  have hw := orthonormal_basis_weights b u hu
  calc
    _ = ∑ j, (∑ i, ⟪b j, u i⟫ ^ 2) * μ j := by
      simp_rw [basis_quadratic_expansion T b μ he]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ _ := fractional_sum_le_sortedTopSum μ _ hk hw.1 hw.2

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def spectralTopSum {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  sortedTopSum hA.eigenvalues k

theorem matrix_orthonormal_trace_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (u : β → EuclideanSpace ℝ n) (hu : Orthonormal ℝ u)
    (hk : Fintype.card β ≤ Fintype.card n) :
    (∑ i, ⟪u i, A.toEuclideanLin (u i)⟫) ≤ spectralTopSum hA (Fintype.card β) := by
  apply orthonormal_trace_le A.toEuclideanLin hA.eigenvectorBasis hA.eigenvalues _ u hu hk
  intro i
  apply PiLp.ext
  intro j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

theorem matrix_orthonormal_trace_bound {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (u : β → EuclideanSpace ℝ n) (hu : Orthonormal ℝ u) :
    (∑ i, ⟪u i, A.toEuclideanLin (u i)⟫) ≤ spectralTopSum hA (Fintype.card β) := by
  apply matrix_orthonormal_trace_le hA u hu
  simpa using hu.linearIndependent.fintype_card_le_finrank

theorem eigenvector_quadratic {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    ⟪hA.eigenvectorBasis i, A.toEuclideanLin (hA.eigenvectorBasis i)⟫ =
      hA.eigenvalues i := by
  have he : A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hA.eigenvectorBasis.orthonormal.norm_eq_one, one_pow, mul_one]

theorem spectralTopSum_mono {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : ∀ x : EuclideanSpace ℝ n, ⟪x, A.toEuclideanLin x⟫ ≤
      ⟪x, B.toEuclideanLin x⟫) {k : ℕ} (hk : k ≤ Fintype.card n) :
    spectralTopSum hA k ≤ spectralTopSum hB k := by
  classical
  let s := topSet hA.eigenvalues k
  have hs : s.card = k := topSet_card _ hk
  let u : s → EuclideanSpace ℝ n := fun i => hA.eigenvectorBasis i.val
  have hu : Orthonormal ℝ u := hA.eigenvectorBasis.orthonormal.comp _ Subtype.val_injective
  have ht := matrix_orthonormal_trace_bound hB u hu
  have hsum : spectralTopSum hA k = ∑ i : s, ⟪u i, A.toEuclideanLin (u i)⟫ := by
    simp only [u, eigenvector_quadratic]
    exact (sortedTopSum_eq_sum_topSet _ _).trans (Finset.sum_coe_sort s _).symm
  rw [hsum]
  calc
    _ ≤ ∑ i : s, ⟪u i, B.toEuclideanLin (u i)⟫ := sum_le_sum fun i _ => hAB _
    _ ≤ _ := by simpa only [Fintype.card_coe, hs] using ht

theorem diagonal_orthonormal_sum_le (d : n → ℝ)
    (u : β → EuclideanSpace ℝ n) (hu : Orthonormal ℝ u)
    (hk : Fintype.card β ≤ Fintype.card n) :
    (∑ i, ∑ j, d j * (u i j) ^ 2) ≤ sortedTopSum d (Fintype.card β) := by
  have hw := orthonormal_basis_weights (EuclideanSpace.basisFun n ℝ) u hu
  have hw' : (∀ j, 0 ≤ (∑ i, (u i j) ^ 2) ∧ (∑ i, (u i j) ^ 2) ≤ 1) ∧
      (∑ j, ∑ i, (u i j) ^ 2) = Fintype.card β := by
    simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
      map_one, one_mul] using hw
  calc
    _ = ∑ j, (∑ i, (u i j) ^ 2) * d j := by
      rw [sum_comm]
      simp_rw [sum_mul, mul_comm (d _)]
    _ ≤ _ := fractional_sum_le_sortedTopSum d _ hk hw'.1 hw'.2

theorem coordinate_quadratic (A : Matrix n n ℝ) (i : n) :
    ⟪EuclideanSpace.basisFun n ℝ i,
      A.toEuclideanLin (EuclideanSpace.basisFun n ℝ i)⟫ = A i i := by
  simp [Matrix.toLpLin_apply, EuclideanSpace.inner_single_left]

theorem spectralTopSum_diagonal_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {k : ℕ} (hk : k ≤ Fintype.card n) :
    sortedTopSum (fun i => A i i) k ≤ spectralTopSum hA k := by
  classical
  let s := topSet (fun i => A i i) k
  have hs : s.card = k := topSet_card _ hk
  let u : s → EuclideanSpace ℝ n := fun i => EuclideanSpace.basisFun n ℝ i.val
  have hu : Orthonormal ℝ u := (EuclideanSpace.basisFun n ℝ).orthonormal.comp _
    Subtype.val_injective
  have ht := matrix_orthonormal_trace_bound hA u hu
  have hsum : sortedTopSum (fun i => A i i) k =
      ∑ i : s, ⟪u i, A.toEuclideanLin (u i)⟫ := by
    simp only [u, coordinate_quadratic]
    exact (sortedTopSum_eq_sum_topSet _ _).trans (Finset.sum_coe_sort s _).symm
  rw [hsum]
  simpa only [Fintype.card_coe, hs] using ht

theorem matrix_inner_dot (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    ⟪x, A.toEuclideanLin x⟫ = x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    dotProduct_comm]

theorem exists_rayleigh_bound [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ n) :
    ∃ i : n, ⟪x, A.toEuclideanLin x⟫ ≤ hA.eigenvalues i * ‖x‖ ^ 2 := by
  obtain ⟨i, _, hi⟩ := exists_max_image (univ : Finset n) hA.eigenvalues univ_nonempty
  have he : ∀ j, A.toEuclideanLin (hA.eigenvectorBasis j) =
      hA.eigenvalues j • hA.eigenvectorBasis j := by
    intro j
    apply PiLp.ext
    intro t
    exact congrFun (hA.mulVec_eigenvectorBasis j) t
  refine ⟨i, ?_⟩
  rw [basis_quadratic_expansion _ _ _ he]
  calc
    _ ≤ ∑ j, hA.eigenvalues i * ⟪hA.eigenvectorBasis j, x⟫ ^ 2 := by
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hi j (mem_univ j)) (sq_nonneg _)
    _ = _ := by rw [← mul_sum, hA.eigenvectorBasis.sum_sq_inner_right]

end Matrix
end ConnectionGraph
