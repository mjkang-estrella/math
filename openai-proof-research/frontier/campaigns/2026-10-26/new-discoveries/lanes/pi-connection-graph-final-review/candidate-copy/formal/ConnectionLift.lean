import GraphScalar
import Variational

open Finset Matrix
open scoped RealInnerProductSpace

namespace ConnectionGraph
noncomputable section

variable {n m ι : Type*} [Fintype n] [Fintype m]

def liftedBlock [DecidableEq n] [DecidableEq m] (U : Matrix n m ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks 1 U Uᵀ (Uᵀ * U - 1)

def rawLift (U : Matrix n m ℝ) (q : ℝ) (u : n → ℝ) : n ⊕ m → ℝ :=
  Sum.elim ((positiveBranch q + 1) • u) (positiveBranch q • (Uᵀ *ᵥ u))

def rawLiftEuclidean (U : Matrix n m ℝ) (q : ℝ) (u : n → ℝ) :
    EuclideanSpace ℝ (n ⊕ m) := WithLp.toLp 2 (rawLift U q u)

theorem rawLift_eigenvector [DecidableEq n] [DecidableEq m]
    (U : Matrix n m ℝ) (q : ℝ) (u : n → ℝ)
    (hu : (U * Uᵀ) *ᵥ u = q • u) :
    liftedBlock U *ᵥ rawLift U q u = positiveBranch q • rawLift U q u := by
  have hp := positiveBranch_equation q
  have hU : U *ᵥ (Uᵀ *ᵥ u) = q • u := by rwa [mulVec_mulVec]
  have hUt : (Uᵀ * U) *ᵥ (Uᵀ *ᵥ u) = q • (Uᵀ *ᵥ u) := by
    rw [← mulVec_mulVec, hU, mulVec_smul]
  rw [liftedBlock, fromBlocks_mulVec]
  simp only [rawLift, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    one_mulVec, mulVec_smul, hU, sub_mulVec, hUt]
  ext (i | j) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  · linear_combination -(u i) * hp
  · linear_combination -((Uᵀ *ᵥ u) j) * hp

theorem transpose_gram_dot (U : Matrix n m ℝ) (u v : n → ℝ) :
    (Uᵀ *ᵥ u) ⬝ᵥ (Uᵀ *ᵥ v) = u ⬝ᵥ ((U * Uᵀ) *ᵥ v) := by
  conv_rhs => rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

theorem rawLift_dot (U : Matrix n m ℝ) (q r : ℝ) (u v : n → ℝ) :
    rawLift U q u ⬝ᵥ rawLift U r v =
      (positiveBranch q + 1) * (positiveBranch r + 1) * (u ⬝ᵥ v) +
      positiveBranch q * positiveBranch r * (u ⬝ᵥ ((U * Uᵀ) *ᵥ v)) := by
  rw [rawLift, rawLift, sumElim_dotProduct_sumElim]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, transpose_gram_dot]
  ring

theorem rawLift_inner (U : Matrix n m ℝ) (q r : ℝ) (u v : n → ℝ) :
    ⟪rawLiftEuclidean U q u, rawLiftEuclidean U r v⟫ =
      (positiveBranch q + 1) * (positiveBranch r + 1) * (u ⬝ᵥ v) +
      positiveBranch q * positiveBranch r * (u ⬝ᵥ ((U * Uᵀ) *ᵥ v)) := by
  rw [real_inner_comm, rawLiftEuclidean, rawLiftEuclidean,
    EuclideanSpace.inner_toLp_toLp]
  simpa only [star_trivial] using rawLift_dot U q r u v

def normalizedLift (U : Matrix n m ℝ) (q : ℝ) (u : n → ℝ) :
    EuclideanSpace ℝ (n ⊕ m) :=
  ‖rawLiftEuclidean U q u‖⁻¹ • rawLiftEuclidean U q u

omit [Fintype m] in
theorem rawLift_ne_zero (U : Matrix n m ℝ) {q : ℝ} (hq : 0 ≤ q)
    {u : n → ℝ} (hu : u ≠ 0) : rawLiftEuclidean U q u ≠ 0 := by
  have hp : positiveBranch q + 1 ≠ 0 := by
    have := positiveBranch_pos hq
    linarith
  intro hz
  apply hu
  funext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (n ⊕ m) => x (Sum.inl i)) hz
  change (positiveBranch q + 1) * u i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left hp

theorem normalizedLift_norm (U : Matrix n m ℝ) {q : ℝ} (hq : 0 ≤ q)
    {u : n → ℝ} (hu : u ≠ 0) : ‖normalizedLift U q u‖ = 1 := by
  have hn : ‖rawLiftEuclidean U q u‖ ≠ 0 := norm_ne_zero_iff.mpr (rawLift_ne_zero U hq hu)
  simp [normalizedLift, norm_smul, hn]

theorem normalizedLift_eigenvector [DecidableEq n] [DecidableEq m]
    (U : Matrix n m ℝ) (q : ℝ) (u : n → ℝ)
    (hu : (U * Uᵀ) *ᵥ u = q • u) :
    (liftedBlock U).toEuclideanLin (normalizedLift U q u) =
      positiveBranch q • normalizedLift U q u := by
  unfold normalizedLift
  rw [map_smul]
  have he : (liftedBlock U).toEuclideanLin (rawLiftEuclidean U q u) =
      positiveBranch q • rawLiftEuclidean U q u := by
    apply PiLp.ext
    intro i
    exact congrFun (rawLift_eigenvector U q u hu) i
  rw [he, smul_comm]

theorem normalizedLift_orthonormal (U : Matrix n m ℝ) (q : ι → ℝ)
    (u : ι → EuclideanSpace ℝ n) (hu : Orthonormal ℝ u)
    (hq : ∀ i, 0 ≤ q i) (he : ∀ i, (U * Uᵀ) *ᵥ (u i).ofLp = q i • (u i).ofLp) :
    Orthonormal ℝ (fun i => normalizedLift U (q i) (u i).ofLp) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte]
    rw [real_inner_self_eq_norm_sq, normalizedLift_norm U (hq i), one_pow]
    intro hz
    apply hu.ne_zero i
    apply PiLp.ext
    intro j
    exact congrFun hz j
  · have huv : (u i).ofLp ⬝ᵥ (u j).ofLp = 0 := by
      have h := hu.inner_eq_zero hij
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
        dotProduct_comm] using h
    have hraw : ⟪rawLiftEuclidean U (q i) (u i).ofLp,
        rawLiftEuclidean U (q j) (u j).ofLp⟫ = 0 := by
      rw [rawLift_inner, he j, dotProduct_smul, huv]
      simp
    simp only [normalizedLift, real_inner_smul_left, real_inner_smul_right, hraw,
      mul_zero, hij, ↓reduceIte]

omit [Fintype n] in
theorem gramHermitian (U : Matrix n m ℝ) : (U * Uᵀ).IsHermitian := by
  simpa using Matrix.isHermitian_mul_conjTranspose_self U

theorem gram_eigenvalues_nonneg [DecidableEq n] (U : Matrix n m ℝ) (i : n) :
    0 ≤ (gramHermitian U).eigenvalues i := by
  simpa using Matrix.eigenvalues_self_mul_conjTranspose_nonneg U i

def positiveLiftFamily [DecidableEq n] (U : Matrix n m ℝ) (i : n) :
    EuclideanSpace ℝ (n ⊕ m) :=
  normalizedLift U ((gramHermitian U).eigenvalues i)
    ((gramHermitian U).eigenvectorBasis i).ofLp

theorem positiveLiftFamily_orthonormal [DecidableEq n] (U : Matrix n m ℝ) :
    Orthonormal ℝ (positiveLiftFamily U) := by
  apply normalizedLift_orthonormal U _ _ (gramHermitian U).eigenvectorBasis.orthonormal
  · exact gram_eigenvalues_nonneg U
  · exact (gramHermitian U).mulVec_eigenvectorBasis

theorem positiveLiftFamily_eigenvector [DecidableEq n] [DecidableEq m]
    (U : Matrix n m ℝ) (i : n) :
    (liftedBlock U).toEuclideanLin (positiveLiftFamily U i) =
      positiveBranch ((gramHermitian U).eigenvalues i) • positiveLiftFamily U i :=
  normalizedLift_eigenvector U _ _ ((gramHermitian U).mulVec_eigenvectorBasis i)

omit [Fintype m] in
theorem liftedBlock_hermitian [DecidableEq n] [DecidableEq m] (U : Matrix n m ℝ) :
    (liftedBlock U).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · exact Matrix.isHermitian_one
  · simp
  · have hg : (Uᵀ * U).IsHermitian := by
      simpa using Matrix.isHermitian_conjTranspose_mul_self U
    exact hg.sub Matrix.isHermitian_one

theorem positiveLiftFamily_quadratic [DecidableEq n] [DecidableEq m]
    (U : Matrix n m ℝ) (i : n) :
    ⟪positiveLiftFamily U i, (liftedBlock U).toEuclideanLin (positiveLiftFamily U i)⟫ =
      positiveBranch ((gramHermitian U).eigenvalues i) := by
  rw [positiveLiftFamily_eigenvector, real_inner_smul_right,
    real_inner_self_eq_norm_sq, (positiveLiftFamily_orthonormal U).norm_eq_one,
    one_pow, mul_one]

theorem selected_positive_branches_le [DecidableEq n] [DecidableEq m]
    (U : Matrix n m ℝ) (s : Finset n) :
    (∑ i ∈ s, positiveBranch ((gramHermitian U).eigenvalues i)) ≤
      spectralTopSum (liftedBlock_hermitian U) s.card := by
  let u : s → EuclideanSpace ℝ (n ⊕ m) := fun i => positiveLiftFamily U i.val
  have hu : Orthonormal ℝ u := (positiveLiftFamily_orthonormal U).comp _ Subtype.val_injective
  have ht := matrix_orthonormal_trace_bound (liftedBlock_hermitian U) u hu
  calc
    _ = ∑ i : s, positiveBranch ((gramHermitian U).eigenvalues i.val) :=
      (Finset.sum_coe_sort s _).symm
    _ ≤ _ := by simpa only [u, positiveLiftFamily_quadratic, Fintype.card_coe] using ht

theorem positive_branches_le_spectralTopSum [DecidableEq n] [DecidableEq m]
    (U : Matrix n m ℝ) {k : ℕ} (hk : k ≤ Fintype.card n) :
    sortedTopSum (fun i => positiveBranch ((gramHermitian U).eigenvalues i)) k ≤
      spectralTopSum (liftedBlock_hermitian U) k := by
  let s := topSet (fun i => positiveBranch ((gramHermitian U).eigenvalues i)) k
  have hs : s.card = k := topSet_card _ hk
  have ht := selected_positive_branches_le U s
  rw [hs] at ht
  exact (sortedTopSum_eq_sum_topSet _ _).trans_le ht

end
end ConnectionGraph
