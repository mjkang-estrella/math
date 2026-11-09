import UnitPath

namespace KadarYu

open Finset
open scoped RealInnerProductSpace

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem orthonormal_combination_norm_sq (u : ι → E) (hu : Orthonormal ℝ u)
    (a : ι → ℝ) : ‖∑ i, a i • u i‖ ^ 2 = ∑ i, a i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := hu.inner_sum a a univ
  simpa [pow_two] using h

theorem orthonormal_eigen_combination_energy (T : E →ₗ[ℝ] E)
    (u : ι → E) (hu : Orthonormal ℝ u) (μ : ι → ℝ)
    (he : ∀ i, T (u i) = μ i • u i) (a : ι → ℝ) :
    ⟪∑ i, a i • u i, T (∑ i, a i • u i)⟫ = ∑ i, μ i * a i ^ 2 := by
  have hT : T (∑ i, a i • u i) = ∑ i, (a i * μ i) • u i := by
    simp only [map_sum, map_smul, he, smul_smul]
  rw [hT, inner_sum]
  apply sum_congr rfl
  intro i _
  rw [inner_smul_right, hu.inner_left_fintype]
  simp
  ring

theorem positive_eigenfamily_projected_li (T : E →ₗ[ℝ] E) (L : E →ₗ[ℝ] F)
    (u : ι → E) (hu : Orthonormal ℝ u) (μ : ι → ℝ) (c : ℝ)
    (he : ∀ i, T (u i) = μ i • u i) (hμ : ∀ i, c < μ i)
    (hker : ∀ x, L x = 0 → ⟪x, T x⟫ ≤ c * ‖x‖ ^ 2) :
    LinearIndependent ℝ (fun i => L (u i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hL : L (∑ j, a j • u j) = 0 := by
    simpa only [map_sum, map_smul] using ha
  have hbound := hker (∑ j, a j • u j) hL
  rw [orthonormal_eigen_combination_energy T u hu μ he,
    orthonormal_combination_norm_sq u hu] at hbound
  have hsum : (∑ j, (μ j - c) * a j ^ 2) ≤ 0 := by
    calc
      _ = (∑ j, μ j * a j ^ 2) - c * ∑ j, a j ^ 2 := by
        simp_rw [sub_mul]
        rw [sum_sub_distrib, mul_sum]
      _ ≤ 0 := sub_nonpos.mpr hbound
  have hsingle : (μ i - c) * a i ^ 2 ≤ ∑ j, (μ j - c) * a j ^ 2 :=
    single_le_sum (fun j _ => mul_nonneg (sub_nonneg.mpr (hμ j).le) (sq_nonneg _))
      (mem_univ i)
  have hsq : a i ^ 2 ≤ 0 := by
    have hp : 0 < μ i - c := sub_pos.mpr (hμ i)
    nlinarith [hsingle.trans hsum, sq_nonneg (a i)]
  nlinarith [sq_nonneg (a i)]

theorem positive_eigenfamily_card_le [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] E) (L : E →ₗ[ℝ] F)
    (u : ι → E) (hu : Orthonormal ℝ u) (μ : ι → ℝ) (c : ℝ)
    (he : ∀ i, T (u i) = μ i • u i) (hμ : ∀ i, c < μ i)
    (hker : ∀ x, L x = 0 → ⟪x, T x⟫ ≤ c * ‖x‖ ^ 2) :
    Fintype.card ι ≤ Module.finrank ℝ F :=
  (positive_eigenfamily_projected_li T L u hu μ c he hμ hker).fintype_card_le_finrank

theorem basis_quadratic_expansion (T : E →ₗ[ℝ] E)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (he : ∀ i, T (b i) = μ i • b i) (x : E) :
    ⟪x, T x⟫ = ∑ i, μ i * ⟪b i, x⟫ ^ 2 := by
  have h := orthonormal_eigen_combination_energy T b b.orthonormal μ he
    (fun i => ⟪b i, x⟫)
  simpa only [b.sum_repr' x] using h

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_eigenbasis_action {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  apply PiLp.ext
  intro j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

noncomputable def spectralCountAbove {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (c : ℝ) : ℕ := by
  classical
  exact (univ.filter fun i => c < hA.eigenvalues i).card

theorem spectralCountAbove_le_target [FiniteDimensional ℝ F]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (L : EuclideanSpace ℝ n →ₗ[ℝ] F) (c : ℝ)
    (hker : ∀ x, L x = 0 → ⟪x, A.toEuclideanLin x⟫ ≤ c * ‖x‖ ^ 2) :
    spectralCountAbove hA c ≤ Module.finrank ℝ F := by
  classical
  let s := univ.filter fun i => c < hA.eigenvalues i
  let u : s → EuclideanSpace ℝ n := fun i => hA.eigenvectorBasis i.val
  have hu : Orthonormal ℝ u :=
    hA.eigenvectorBasis.orthonormal.comp _ Subtype.val_injective
  have he : ∀ i : s, A.toEuclideanLin (u i) = hA.eigenvalues i.val • u i :=
    fun i => matrix_eigenbasis_action hA i.val
  have hp : ∀ i : s, c < hA.eigenvalues i.val :=
    fun i => (mem_filter.mp i.property).2
  have h := positive_eigenfamily_card_le A.toEuclideanLin L u hu
    (fun i : s => hA.eigenvalues i.val) c he hp hker
  change s.card ≤ Module.finrank ℝ F
  simpa only [Fintype.card_coe] using h

theorem quadratic_le_of_above_coordinates_zero {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (c : ℝ) (x : EuclideanSpace ℝ n)
    (hz : ∀ i, c < hA.eigenvalues i → ⟪hA.eigenvectorBasis i, x⟫ = 0) :
    ⟪x, A.toEuclideanLin x⟫ ≤ c * ‖x‖ ^ 2 := by
  rw [basis_quadratic_expansion A.toEuclideanLin hA.eigenvectorBasis hA.eigenvalues
    (matrix_eigenbasis_action hA)]
  calc
    _ ≤ ∑ i, c * ⟪hA.eigenvectorBasis i, x⟫ ^ 2 := by
      apply sum_le_sum
      intro i _
      by_cases hi : c < hA.eigenvalues i
      · rw [hz i hi]
        simp
      · exact mul_le_mul_of_nonneg_right (le_of_not_gt hi) (sq_nonneg _)
    _ = c * ‖x‖ ^ 2 := by rw [← mul_sum, hA.eigenvectorBasis.sum_sq_inner_right]

end Matrix

theorem spectralCountAbove_mono_isometry
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix m m ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (e : EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ m) (c : ℝ)
    (hform : ∀ x, ⟪x, A.toEuclideanLin x⟫ ≤ ⟪e x, B.toEuclideanLin (e x)⟫) :
    spectralCountAbove hA c ≤ spectralCountAbove hB c := by
  classical
  let s := univ.filter fun i => c < hB.eigenvalues i
  let L : EuclideanSpace ℝ n →ₗ[ℝ] (s → ℝ) :=
    LinearMap.pi fun i => ((innerSL ℝ (hB.eigenvectorBasis i.val)).toLinearMap).comp
      e.toLinearMap
  have hker : ∀ x, L x = 0 → ⟪x, A.toEuclideanLin x⟫ ≤ c * ‖x‖ ^ 2 := by
    intro x hx
    have hz : ∀ i, c < hB.eigenvalues i → ⟪hB.eigenvectorBasis i, e x⟫ = 0 := by
      intro i hi
      have his : i ∈ s := mem_filter.mpr ⟨mem_univ i, hi⟩
      exact congrFun hx ⟨i, his⟩
    calc
      _ ≤ ⟪e x, B.toEuclideanLin (e x)⟫ := hform x
      _ ≤ c * ‖e x‖ ^ 2 := quadratic_le_of_above_coordinates_zero hB c (e x) hz
      _ = c * ‖x‖ ^ 2 := by rw [e.norm_map]
  have h := spectralCountAbove_le_target hA L c hker
  change spectralCountAbove hA c ≤ s.card
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h

end KadarYu
