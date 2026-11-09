import GraphMatrices
import Variational

/-!
# Positive Dirac eigenvectors: normalization and degree-based spectral upper bounds

Implementation lane `pi-connection-dirac-formal`. This file is INFRASTRUCTURE for the
connection-graph/Dirac comparison campaign: no discovery credit is claimed for any
result here. Everything is classical finite-dimensional linear algebra.

Main content:

* `ConnectionGraph.diracPos_orthonormal` and `ConnectionGraph.diracPos_eigenvector`:
  given an orthonormal family `w i = (a i, b i)` of *positive* eigenvectors of the
  block operator `[[0, C], [Cᵀ, 0]]` with eigenvalues `μ i > 0`, the scaled vertex
  components `√2 • a i` form an orthonormal family of eigenvectors of `C * Cᵀ` with
  eigenvalues `μ i ^ 2`. The proof uses only adjointness and needs neither a rank
  statement nor a zero-multiplicity count; repeated eigenvalues are allowed.

* `ConnectionGraph.sortedTopSum_mono_of_nonneg`: the top sums of a nonnegative
  array are monotone in `k`.

* `ConnectionGraph.dirac_spectral_top_sum_le_sqrt`: for a finite graph with edge
  set `E` on `v` vertices, every top-`k` spectral sum of the Dirac matrix
  `[[0, C],[Cᵀ, 0]]` (`C = signedIncidence E`), `k ≤ v`, is at most
  `√(2 k T_k)` where `T_k = sortedTopSum (degree E) k`.

* `ConnectionGraph.dirac_spectral_top_sum_le_global`: for every `k ≤ v + m`
  the top-`k` spectral sum of the Dirac matrix is at most `m + v / 2`.
-/

open Finset Matrix
open scoped RealInnerProductSpace

namespace ConnectionGraph

variable {V F ι : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  [Fintype ι]

noncomputable section

/-! ## The normalized positive-eigenvector construction -/

omit [DecidableEq V] [DecidableEq F] in
/-- The vertex component of a block vector, as an element of `EuclideanSpace ℝ V`. -/
def diracVertComp (w : ι → EuclideanSpace ℝ (V ⊕ F)) (i : ι) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 fun x => w i (Sum.inl x)

/-- The edge component of a block vector, as an element of `EuclideanSpace ℝ F`. -/
def diracEdgeComp (w : ι → EuclideanSpace ℝ (V ⊕ F)) (i : ι) : EuclideanSpace ℝ F :=
  WithLp.toLp 2 fun e => w i (Sum.inr e)

/-- The normalized positive Dirac eigenvector living on the vertex space:
`√2 • a i`. Its inner products reproduce those of `w` exactly. -/
def diracNormalized (w : ι → EuclideanSpace ℝ (V ⊕ F)) (i : ι) : EuclideanSpace ℝ V :=
  (√2 : ℝ) • diracVertComp w i

omit [DecidableEq V] [DecidableEq F] in
/-- Action of the block operator `[[0, C], [Cᵀ, 0]]` on a vertex coordinate. -/
theorem fromBlocks_dirac_apply_inl (C : Matrix V F ℝ) (w : EuclideanSpace ℝ (V ⊕ F))
    (x : V) :
    ((fromBlocks 0 C Cᵀ 0) *ᵥ w) (Sum.inl x) = (C *ᵥ (fun e => w (Sum.inr e))) x := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type]

omit [DecidableEq V] [DecidableEq F] in
/-- Action of the block operator `[[0, C], [Cᵀ, 0]]` on an edge coordinate. -/
theorem fromBlocks_dirac_apply_inr (C : Matrix V F ℝ) (w : EuclideanSpace ℝ (V ⊕ F))
    (e : F) :
    ((fromBlocks 0 C Cᵀ 0) *ᵥ w) (Sum.inr e) = (Cᵀ *ᵥ (fun x => w (Sum.inl x))) e := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, transpose_apply]

omit [Fintype ι] in
omit [DecidableEq V] [DecidableEq F] in
/-- `A.toEuclideanLin v` is the lift of `A *ᵥ v`. -/
theorem toEuclideanLin_eq {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (D : Matrix m n ℝ) (v : EuclideanSpace ℝ n) :
    D.toEuclideanLin v = WithLp.toLp 2 (D *ᵥ v) := rfl

omit [DecidableEq V] [DecidableEq F] in
/-- The Euclidean inner product of two block vectors splits over `V ⊕ F`, and the
resulting pieces are the dot products of the components. -/
theorem dirac_inner_split (w z : EuclideanSpace ℝ (V ⊕ F)) :
    ⟪w, z⟫ = (fun x => w (Sum.inl x)) ⬝ᵥ (fun x => z (Sum.inl x))
      + (fun e => w (Sum.inr e)) ⬝ᵥ (fun e => z (Sum.inr e)) := by
  simp [PiLp.inner_apply, dotProduct, Fintype.sum_sum_type, mul_comm]

/-- The Euclidean inner product on `EuclideanSpace ℝ n` is the dot product of the
underlying functions. -/
theorem euclid_inner_dot {n : Type*} [Fintype n] (x y : EuclideanSpace ℝ n) :
    ⟪x, y⟫ = (x : n → ℝ) ⬝ᵥ (y : n → ℝ) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

omit [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype ι] in
/-- The vertex component inner product is the dot product of the raw components. -/
theorem diracVertComp_inner (w z : ι → EuclideanSpace ℝ (V ⊕ F)) (i j : ι) :
    ⟪diracVertComp w i, diracVertComp z j⟫
      = (fun x => w i (Sum.inl x)) ⬝ᵥ (fun x => z j (Sum.inl x)) := by
  unfold diracVertComp
  rw [euclid_inner_dot]

omit [DecidableEq V] [DecidableEq F] in
/-- Adjointness of multiplication by `C` and by `Cᵀ` (real dot products). -/
theorem dotProduct_adjoint (C : Matrix V F ℝ) (a : V → ℝ) (b : F → ℝ) :
    a ⬝ᵥ (C *ᵥ b) = (Cᵀ *ᵥ a) ⬝ᵥ b := by
  simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => by ring

omit [Fintype ι] in
/-- The two block equations extracted from a Dirac eigenvector equation. -/
theorem diracPos_block_eq (C : Matrix V F ℝ) (w : EuclideanSpace ℝ (V ⊕ F)) (μ : ℝ)
    (h : (fromBlocks 0 C Cᵀ 0).toEuclideanLin w = μ • w) :
    C *ᵥ (fun e => w (Sum.inr e)) = μ • (fun x => w (Sum.inl x)) ∧
      Cᵀ *ᵥ (fun x => w (Sum.inl x)) = μ • (fun e => w (Sum.inr e)) := by
  constructor
  · funext x
    have h1 : ((fromBlocks 0 C Cᵀ 0) *ᵥ w) (Sum.inl x) = (μ • w) (Sum.inl x) :=
      congrArg (fun v : EuclideanSpace ℝ (V ⊕ F) => v (Sum.inl x)) h
    rw [fromBlocks_dirac_apply_inl] at h1
    simpa using h1
  · funext e
    have h1 : ((fromBlocks 0 C Cᵀ 0) *ᵥ w) (Sum.inr e) = (μ • w) (Sum.inr e) :=
      congrArg (fun v : EuclideanSpace ℝ (V ⊕ F) => v (Sum.inr e)) h
    rw [fromBlocks_dirac_apply_inr] at h1
    simpa using h1

omit [Fintype ι] in
/-- Key normalization identity: for positive eigenvalues the vertex component inner
product equals half the block inner product. -/
theorem diracPos_inner_half (C : Matrix V F ℝ) (w z : ι → EuclideanSpace ℝ (V ⊕ F))
    (μ ν : ι → ℝ) (i j : ι) (hμ : 0 < μ i) (hν : 0 < ν j)
    (h : (fromBlocks 0 C Cᵀ 0).toEuclideanLin (w i) = μ i • w i)
    (h' : (fromBlocks 0 C Cᵀ 0).toEuclideanLin (z j) = ν j • z j) :
    ⟪diracVertComp w i, diracVertComp z j⟫ = ⟪w i, z j⟫ / 2 := by
  obtain ⟨hb1, hb2⟩ := diracPos_block_eq C (w i) (μ i) h
  obtain ⟨hb1', hb2'⟩ := diracPos_block_eq C (z j) (ν j) h'
  set p : ℝ := (fun x => w i (Sum.inl x)) ⬝ᵥ (fun x => z j (Sum.inl x)) with hp
  set q : ℝ := (fun e => w i (Sum.inr e)) ⬝ᵥ (fun e => z j (Sum.inr e)) with hq
  -- E1: μ i * p = ν j * q
  have E1 : μ i * p = ν j * q := by
    have t1 := dotProduct_adjoint C (fun x => z j (Sum.inl x)) (fun e => w i (Sum.inr e))
    rw [hb1, hb2'] at t1
    simp only [dotProduct_smul, smul_dotProduct] at t1
    rw [dotProduct_comm (fun x => z j (Sum.inl x)) (fun x => w i (Sum.inl x)),
      dotProduct_comm (fun e => z j (Sum.inr e)) (fun e => w i (Sum.inr e))] at t1
    exact t1
  -- E2: ν j * p = μ i * q
  have E2 : ν j * p = μ i * q := by
    have t1 := dotProduct_adjoint C (fun x => w i (Sum.inl x)) (fun e => z j (Sum.inr e))
    rw [hb1', hb2] at t1
    simp only [dotProduct_smul, smul_dotProduct] at t1
    exact t1
  have hpos : (0 : ℝ) < μ i + ν j := add_pos hμ hν
  have hpq : p = q := by
    refine mul_right_cancel₀ (ne_of_gt hpos) ?_
    linear_combination (E1 + E2)
  have hsplit := dirac_inner_split (w i) (z j)
  rw [← hp, ← hq] at hsplit
  rw [diracVertComp_inner]
  linarith

omit [Fintype ι] in
/-- The normalized vertex components form an orthonormal family. -/
theorem diracPos_orthonormal (C : Matrix V F ℝ) (w : ι → EuclideanSpace ℝ (V ⊕ F))
    (μ : ι → ℝ) (hw : Orthonormal ℝ w) (hμ : ∀ i, 0 < μ i)
    (h : ∀ i, (fromBlocks 0 C Cᵀ 0).toEuclideanLin (w i) = μ i • w i) :
    Orthonormal ℝ (diracNormalized w) := by
  have h22 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  constructor
  · intro i
    have h1 : ⟪diracNormalized w i, diracNormalized w i⟫ = ⟪w i, w i⟫ := by
      unfold diracNormalized
      rw [real_inner_smul_left, real_inner_smul_right,
        diracPos_inner_half C w w μ μ i i (hμ i) (hμ i) (h i) (h i),
        real_inner_self_eq_norm_sq, hw.1 i, ← mul_assoc, h22]
      norm_num
    have h2 : ‖diracNormalized w i‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, h1, real_inner_self_eq_norm_sq, hw.1 i]
      norm_num
    have h3 : 0 ≤ ‖diracNormalized w i‖ := norm_nonneg _
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact h
    · linarith
  · intro i j hij
    have h1 : ⟪diracNormalized w i, diracNormalized w j⟫ = ⟪w i, w j⟫ := by
      unfold diracNormalized
      rw [real_inner_smul_left, real_inner_smul_right,
        diracPos_inner_half C w w μ μ i j (hμ i) (hμ j) (h i) (h j), ← mul_assoc,
        h22]
      ring
    rw [h1]
    exact hw.2 hij

omit [Fintype ι] in
/-- The normalized vertex components are eigenvectors of `C * Cᵀ` with eigenvalues
`μ i ^ 2`. -/
theorem diracPos_eigenvector (C : Matrix V F ℝ) (w : ι → EuclideanSpace ℝ (V ⊕ F))
    (μ : ι → ℝ)
    (h : ∀ i, (fromBlocks 0 C Cᵀ 0).toEuclideanLin (w i) = μ i • w i) (i : ι) :
    (C * Cᵀ).toEuclideanLin (diracNormalized w i) = μ i ^ 2 • diracNormalized w i := by
  obtain ⟨hb1, hb2⟩ := diracPos_block_eq C (w i) (μ i) (h i)
  have key : (C * Cᵀ) *ᵥ (fun x => w i (Sum.inl x))
      = (μ i * μ i) • (fun x => w i (Sum.inl x)) := by
    rw [← Matrix.mulVec_mulVec, hb2, Matrix.mulVec_smul, hb1, smul_smul]
  refine PiLp.ext fun x => ?_
  have h0 : (C * Cᵀ).toEuclideanLin (diracNormalized w i) x
      = ((C * Cᵀ) *ᵥ (diracNormalized w i)) x := rfl
  rw [h0]
  simp only [diracNormalized, diracVertComp, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec_smul]
  rw [key, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Generic helper inequalities -/

/-- Cauchy–Schwarz: the square of a finite sum is at most the cardinality times the
sum of squares. -/
theorem sq_sum_le_card_mul_sq_sum {β : Type*} [Fintype β] (a : β → ℝ) :
    (∑ i, a i) ^ 2 ≤ (Fintype.card β : ℝ) * ∑ i, a i ^ 2 := by
  set x : EuclideanSpace ℝ β := WithLp.toLp 2 a with hx
  set y : EuclideanSpace ℝ β := WithLp.toLp 2 (fun _ => (1 : ℝ)) with hy
  have hxy : ⟪x, y⟫ = ∑ i, a i := by
    simp [PiLp.inner_apply, hx, hy]
  have hnx : ‖x‖ ^ 2 = ∑ i, a i ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [hx]
  have hny : ‖y‖ ^ 2 = (Fintype.card β : ℝ) := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [hy]
  have h1 := abs_real_inner_le_norm (x := x) (y := y)
  have h2 : ⟪x, y⟫ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    obtain ⟨ha, hb⟩ := abs_le.mp h1
    exact sq_le_sq' ha hb
  calc (∑ i, a i) ^ 2 = ⟪x, y⟫ ^ 2 := by rw [hxy]
    _ ≤ (‖x‖ * ‖y‖) ^ 2 := h2
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by ring
    _ = (Fintype.card β : ℝ) * ∑ i, a i ^ 2 := by rw [hnx, hny]; ring

/-- A finite sum is bounded by the square root of cardinality times sum of squares. -/
theorem sum_le_sqrt_card_mul_sq_sum {β : Type*} [Fintype β] (a : β → ℝ) :
    ∑ i, a i ≤ Real.sqrt ((Fintype.card β : ℝ) * ∑ i, a i ^ 2) := by
  rcases le_or_gt (0 : ℝ) (∑ i, a i) with h0 | h0
  · exact (Real.le_sqrt h0 (by positivity)).mpr (sq_sum_le_card_mul_sq_sum a)
  · linarith [Real.sqrt_nonneg ((Fintype.card β : ℝ) * ∑ i, a i ^ 2)]

/-- Dropping the nonpositive entries of a finite sum can only increase it. -/
theorem sum_le_sum_pos_part {α : Type*} [DecidableEq α] (f : α → ℝ) (S : Finset α) :
    (∑ i ∈ S, f i) ≤ ∑ i ∈ S.filter (fun i => 0 < f i), f i := by
  classical
  have hsplit : (∑ i ∈ S, f i)
      = (∑ i ∈ S.filter (fun i => 0 < f i), f i)
        + (∑ i ∈ S.filter (fun i => ¬ (0 < f i)), f i) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have h2 : (∑ i ∈ S.filter (fun i => ¬ (0 < f i)), f i) ≤ 0 := by
    refine sum_nonpos fun i hi => ?_
    exact not_lt.mp (Finset.mem_filter.mp hi).2
  rw [hsplit]
  linarith

/-- Top sums of a nonnegative array are monotone in the cutoff. -/
theorem sortedTopSum_mono_of_nonneg {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ)
    (hf : ∀ i, 0 ≤ f i) {r k : ℕ}
    (hrk : r ≤ k) :
    sortedTopSum f r ≤ sortedTopSum f k := by
  rw [sortedTopSum_eq_sum_topSet, sortedTopSum_eq_sum_topSet]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hf i)
  intro i hi
  have hi' : i ∈ (descendingIndices f).take r := List.mem_toFinset.mp hi
  have htk : ((descendingIndices f).take k).take r = (descendingIndices f).take r := by
    rw [List.take_take, Nat.min_eq_left hrk]
  exact List.mem_toFinset.mpr (List.mem_of_mem_take (htk.symm ▸ hi'))

/-! ## Graph upper bounds for the Dirac spectrum -/

section Graph

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Each signed-incidence column has squared norm exactly `2`. -/
theorem signedIncidence_column_sq {E : Finset (V × V)} (hE : ValidEdges E) (e : E) :
    ∑ x, (signedIncidence E x e) ^ 2 = 2 := by
  have hne := edge_ne hE e
  have h1 : ∀ x : V, (signedIncidence E x e) ^ 2
      = (if x = e.val.1 then 1 else 0) + (if x = e.val.2 then 1 else 0) := by
    intro x
    by_cases hx1 : x = e.val.1
    · subst hx1
      simp [signedIncidence, hne]
    · by_cases hx2 : x = e.val.2
      · subst hx2
        simp [signedIncidence, hne.symm]
      · simp [signedIncidence, hx1, hx2]
  rw [Finset.sum_congr rfl fun x _ => h1 x]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
  ring

/-- Bessel-type bound: an orthonormal family in the vertex space has total
Dirac energy at most `2 * #E`. -/
theorem diracPos_ON_energy_le {E : Finset (V × V)} (hE : ValidEdges E)
    (u : ι → EuclideanSpace ℝ V)
    (hu : Orthonormal ℝ u) :
    (∑ i, ⟪u i, (graphLaplacian E).toEuclideanLin (u i)⟫) ≤ 2 * (E.card : ℝ) := by
  classical
  have hcol : ∀ e : E, ‖(WithLp.toLp 2 (fun x => signedIncidence E x e) :
      EuclideanSpace ℝ V)‖ ^ 2 = 2 := by
    intro e
    rw [PiLp.norm_sq_eq_of_L2]
    simp [signedIncidence_column_sq hE e]
  have htrans : ∀ (v : EuclideanSpace ℝ V) (e : E),
      ((signedIncidence E)ᵀ *ᵥ v) e
        = ⟪(WithLp.toLp 2 (fun x => signedIncidence E x e) : EuclideanSpace ℝ V), v⟫ := by
    intro v e
    simp [PiLp.inner_apply, dotProduct, mulVec, mul_comm]
  have hstep : ∀ i : ι, ⟪u i, (graphLaplacian E).toEuclideanLin (u i)⟫
      = ∑ e : E, (((signedIncidence E)ᵀ *ᵥ (u i)) e) ^ 2 := by
    intro i
    have h1 : ⟪u i, (graphLaplacian E).toEuclideanLin (u i)⟫
        = (u i : V → ℝ) ⬝ᵥ ((graphLaplacian E) *ᵥ (u i : V → ℝ)) := by
      simp [euclid_inner_dot, toEuclideanLin_eq]
    rw [h1, signed_energy]
    exact Finset.sum_congr rfl fun e _ => by rw [signed_transpose_mulVec]
  calc ∑ i, ⟪u i, (graphLaplacian E).toEuclideanLin (u i)⟫
      = ∑ e : E, ∑ i : ι, (((signedIncidence E)ᵀ *ᵥ (u i)) e) ^ 2 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => hstep i
    _ ≤ ∑ e : E, ‖(WithLp.toLp 2 (fun x => signedIncidence E x e) :
          EuclideanSpace ℝ V)‖ ^ 2 := by
        refine Finset.sum_le_sum fun e _ => ?_
        have hb := hu.sum_inner_products_le (s := (univ : Finset ι))
          (x := ((WithLp.toLp 2 (fun x => signedIncidence E x e) :
            EuclideanSpace ℝ V)))
        -- hb : ∑ i ∈ univ, ‖⟪u i, column e⟫‖ ^ 2 ≤ ‖column e‖ ^ 2
        have hb2 : ∀ i : ι, (((signedIncidence E)ᵀ *ᵥ (u i)) e) ^ 2
            = ‖⟪u i, (WithLp.toLp 2 (fun x => signedIncidence E x e) :
              EuclideanSpace ℝ V)⟫‖ ^ 2 := by
          intro i
          rw [htrans, real_inner_comm]
          simp
        simp only [hb2]
        exact hb
    _ = 2 * (E.card : ℝ) := by
        rw [Finset.sum_congr rfl fun e (_ : e ∈ (univ : Finset E)) => hcol e]
        simp
        ring

/-- First endpoint: for `k ≤ v`, every top-`k` spectral sum of the Dirac block
matrix of a graph is at most `√(2 k T_k)`, `T_k = sortedTopSum (degree E) k`. -/
theorem dirac_spectral_top_sum_le_sqrt (E : Finset (V × V)) {k : ℕ}
    (hk : k ≤ Fintype.card V) :
    spectralTopSum (dirac_hermitian E) k
      ≤ Real.sqrt (2 * (k : ℝ) * sortedTopSum (degree E) k) := by
  classical
  set hD := dirac_hermitian E
  -- cardinality bookkeeping
  have hDcard : k ≤ Fintype.card (V ⊕ E) := by
    have h1 := Fintype.card_sum (α := V) (β := ↥E)
    omega
  set S := topSet hD.eigenvalues k with hSdef
  have hScard : S.card = k := topSet_card hD.eigenvalues hDcard
  have hspec : spectralTopSum hD k = ∑ i ∈ S, hD.eigenvalues i :=
    sortedTopSum_eq_sum_topSet _ _
  set Sp := S.filter fun i => 0 < hD.eigenvalues i with hSpdef
  -- the positive part of the top-k set
  have hdrop : (∑ i ∈ S, hD.eigenvalues i) ≤ ∑ i ∈ Sp, hD.eigenvalues i :=
    sum_le_sum_pos_part _ _
  -- orthonormal family of positive eigenvectors, indexed by ↥Sp
  have hw : Orthonormal ℝ (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) :=
    hD.eigenvectorBasis.orthonormal.comp _ Subtype.val_injective
  have hμ : ∀ i : ↥Sp, 0 < hD.eigenvalues (i : V ⊕ E) := by
    intro i
    exact (Finset.mem_filter.mp i.2).2
  have hev : ∀ i : ↥Sp,
      (fromBlocks 0 (signedIncidence E) (signedIncidence E)ᵀ 0).toEuclideanLin
        (hD.eigenvectorBasis (i : V ⊕ E)) = hD.eigenvalues (i : V ⊕ E) •
        hD.eigenvectorBasis (i : V ⊕ E) := by
    intro i
    have h1 := hD.mulVec_eigenvectorBasis (i : V ⊕ E)
    rw [← dirac_block E, toEuclideanLin_eq]
    exact congrArg (WithLp.toLp 2) h1
  -- normalized family on the vertex space
  have horth : Orthonormal ℝ
      (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E))) :=
    diracPos_orthonormal (signedIncidence E) _ _ hw hμ hev
  have hvec : ∀ i : ↥Sp,
      (signedIncidence E * (signedIncidence E)ᵀ).toEuclideanLin
        (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i)
        = hD.eigenvalues (i : V ⊕ E) ^ 2 •
        diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i :=
    diracPos_eigenvector (signedIncidence E) _ _ hev
  -- cardinality bookkeeping for the family
  have hrk : Sp.card ≤ k := by
    calc Sp.card ≤ S.card := Finset.card_filter_le _ _
      _ = k := hScard
  have hrcard : Fintype.card ↥Sp ≤ Fintype.card V := by
    have h1 : Fintype.card ↥Sp = Sp.card := by simp
    omega
  -- each eigenvalue contributes μ² to the Dirac energy on the vertex space
  have hGE : (graphLaplacian E).toEuclideanLin
      = (signedIncidence E * (signedIncidence E)ᵀ).toEuclideanLin := rfl
  have hquad : ∀ i : ↥Sp,
      ⟪diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i,
        (graphLaplacian E).toEuclideanLin
          (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i)⟫
        = hD.eigenvalues (i : V ⊕ E) ^ 2 := by
    intro i
    rw [hGE, hvec i, real_inner_smul_right]
    have h1 : ⟪diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i,
      diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, horth.1 i]
      norm_num
    rw [h1]
    ring
  -- the Ky Fan diagonal bound
  have hdiag : (∑ i : ↥Sp, ∑ x, degree E x *
      (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i) x ^ 2)
      ≤ sortedTopSum (degree E) Sp.card := by
    have h := diagonal_orthonormal_sum_le (d := degree E)
      (u := diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)))
      horth hrcard
    rwa [Fintype.card_coe] at h
  have hsq : ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2
      ≤ 2 * sortedTopSum (degree E) Sp.card := by
    have h1 : ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2
        = ∑ i : ↥Sp, ⟪diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i,
          (graphLaplacian E).toEuclideanLin
            (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i)⟫ := by
      exact Finset.sum_congr rfl fun i _ => (hquad i).symm
    rw [h1]
    calc ∑ i : ↥Sp, ⟪diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i,
          (graphLaplacian E).toEuclideanLin
            (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i)⟫
        ≤ ∑ i : ↥Sp, (2 * ∑ x, degree E x *
            (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i) x ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [euclid_inner_dot]
          exact graph_degree_quadratic_bound E _
      _ = 2 * ∑ i : ↥Sp, ∑ x, degree E x *
            (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i) x ^ 2 := by
          rw [← Finset.mul_sum]
      _ ≤ 2 * sortedTopSum (degree E) Sp.card := by
          exact mul_le_mul_of_nonneg_left hdiag (by positivity)
  -- Cauchy–Schwarz and monotonicity give the bound
  have hkey : (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E))
      ≤ Real.sqrt (2 * (k : ℝ) * sortedTopSum (degree E) k) := by
    have e1 : (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E)) ^ 2
        ≤ (Fintype.card ↥Sp : ℝ) * ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2 :=
      sq_sum_le_card_mul_sq_sum _
    have e2 : (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2)
        ≤ 2 * sortedTopSum (degree E) Sp.card := hsq
    have e3 : (Fintype.card ↥Sp : ℝ) ≤ (k : ℝ) := by
      have h1 : Fintype.card ↥Sp = Sp.card := by simp
      exact_mod_cast (h1.trans_le hrk)
    have e4 := sortedTopSum_mono_of_nonneg (degree E) (degree_nonneg E) hrk
    have hTpos1 : 0 ≤ sortedTopSum (degree E) Sp.card := by
      rw [sortedTopSum_eq_sum_topSet]
      exact sum_nonneg fun i _ => degree_nonneg E i
    have hTposk : 0 ≤ sortedTopSum (degree E) k := by
      rw [sortedTopSum_eq_sum_topSet]
      exact sum_nonneg fun i _ => degree_nonneg E i
    have h1 : (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E)) ^ 2
        ≤ 2 * (k : ℝ) * sortedTopSum (degree E) k := by
      calc (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E)) ^ 2
          ≤ (Fintype.card ↥Sp : ℝ) * ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2 := e1
        _ ≤ (Fintype.card ↥Sp : ℝ) * (2 * sortedTopSum (degree E) Sp.card) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = 2 * ((Fintype.card ↥Sp : ℝ) * sortedTopSum (degree E) Sp.card) := by ring
        _ ≤ 2 * ((k : ℝ) * sortedTopSum (degree E) k) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc (Fintype.card ↥Sp : ℝ) * sortedTopSum (degree E) Sp.card
                ≤ (k : ℝ) * sortedTopSum (degree E) Sp.card :=
                  mul_le_mul_of_nonneg_right e3 hTpos1
              _ ≤ (k : ℝ) * sortedTopSum (degree E) k :=
                  mul_le_mul_of_nonneg_left e4 (Nat.cast_nonneg _)
        _ = 2 * (k : ℝ) * sortedTopSum (degree E) k := by ring
    refine (Real.le_sqrt (sum_nonneg fun i _ => le_of_lt (hμ i)) ?_).mpr h1
    exact mul_nonneg (by norm_num) hTposk
  -- conclude
  rw [hspec]
  calc ∑ i ∈ S, hD.eigenvalues i ≤ ∑ i ∈ Sp, hD.eigenvalues i := hdrop
    _ = ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) := (Finset.sum_coe_sort Sp _).symm
    _ ≤ Real.sqrt (2 * (k : ℝ) * sortedTopSum (degree E) k) := hkey

/-- Second endpoint: for every `k ≤ v + m`, the top-`k` spectral sum of the Dirac
block matrix is at most `m + v / 2`. -/
theorem dirac_spectral_top_sum_le_global (E : Finset (V × V)) (hE : ValidEdges E)
    {k : ℕ} (hk : k ≤ Fintype.card (V ⊕ E)) :
    spectralTopSum (dirac_hermitian E) k
      ≤ (E.card : ℝ) + (Fintype.card V : ℝ) / 2 := by
  classical
  set hD := dirac_hermitian E
  set S := topSet hD.eigenvalues k with hSdef
  have hScard : S.card = k := topSet_card hD.eigenvalues hk
  have hspec : spectralTopSum hD k = ∑ i ∈ S, hD.eigenvalues i :=
    sortedTopSum_eq_sum_topSet _ _
  set Sp := S.filter fun i => 0 < hD.eigenvalues i with hSpdef
  have hdrop : (∑ i ∈ S, hD.eigenvalues i) ≤ ∑ i ∈ Sp, hD.eigenvalues i :=
    sum_le_sum_pos_part _ _
  have hw : Orthonormal ℝ (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) :=
    hD.eigenvectorBasis.orthonormal.comp _ Subtype.val_injective
  have hμ : ∀ i : ↥Sp, 0 < hD.eigenvalues (i : V ⊕ E) := by
    intro i
    exact (Finset.mem_filter.mp i.2).2
  have hev : ∀ i : ↥Sp,
      (fromBlocks 0 (signedIncidence E) (signedIncidence E)ᵀ 0).toEuclideanLin
        (hD.eigenvectorBasis (i : V ⊕ E)) = hD.eigenvalues (i : V ⊕ E) •
        hD.eigenvectorBasis (i : V ⊕ E) := by
    intro i
    have h1 := hD.mulVec_eigenvectorBasis (i : V ⊕ E)
    rw [← dirac_block E, toEuclideanLin_eq]
    exact congrArg (WithLp.toLp 2) h1
  have horth : Orthonormal ℝ
      (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E))) :=
    diracPos_orthonormal (signedIncidence E) _ _ hw hμ hev
  have hrcard : Fintype.card ↥Sp ≤ Fintype.card V := by
    have hlin : LinearIndependent ℝ (fun i : ↥Sp =>
        diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i) :=
      horth.linearIndependent
    have hdim := hlin.fintype_card_le_finrank (R := ℝ)
      (M := EuclideanSpace ℝ V) (b := fun i : ↥Sp =>
        diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i)
    rwa [finrank_euclideanSpace] at hdim
  -- sum of squares is at most the trace 2m
  have hsq2 : ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2 ≤ 2 * (E.card : ℝ) := by
    have hGE : (graphLaplacian E).toEuclideanLin
        = (signedIncidence E * (signedIncidence E)ᵀ).toEuclideanLin := rfl
    have h1 := diracPos_ON_energy_le hE
      (fun i : ↥Sp => diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i)
      horth
    have h2 : ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2
        = ∑ i : ↥Sp, ⟪diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i,
          (graphLaplacian E).toEuclideanLin
            (diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i)⟫ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hGE, diracPos_eigenvector (signedIncidence E)
        (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E))
        (fun i => hD.eigenvalues (i : V ⊕ E)) hev i, real_inner_smul_right]
      have h3 : ⟪diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i,
        diracNormalized (fun i : ↥Sp => hD.eigenvectorBasis (i : V ⊕ E)) i⟫ = 1 := by
        rw [real_inner_self_eq_norm_sq, horth.1 i]
        norm_num
      rw [h3]
      ring
    rw [h2]
    exact h1
  -- 2μ ≤ μ² + 1 termwise, summed
  have hsum1 : 2 * (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E))
      ≤ ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2 + (Fintype.card ↥Sp : ℝ) := by
    have hterm : ∀ i : ↥Sp, 2 * hD.eigenvalues (i : V ⊕ E)
        ≤ hD.eigenvalues (i : V ⊕ E) ^ 2 + 1 := by
      intro i
      nlinarith [sq_nonneg (hD.eigenvalues (i : V ⊕ E) - 1)]
    have h3 : 2 * (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E))
        = ∑ i : ↥Sp, 2 * hD.eigenvalues (i : V ⊕ E) :=
      Finset.mul_sum _ _ _
    have h4 : (∑ i : ↥Sp, 2 * hD.eigenvalues (i : V ⊕ E))
        ≤ ∑ i : ↥Sp, (hD.eigenvalues (i : V ⊕ E) ^ 2 + 1) :=
      Finset.sum_le_sum fun i _ => hterm i
    have h5 : (∑ i : ↥Sp, (hD.eigenvalues (i : V ⊕ E) ^ 2 + 1))
        = ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2 + (Fintype.card ↥Sp : ℝ) := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp
    rw [h3]
    linarith
  -- conclude
  rw [hspec]
  calc ∑ i ∈ S, hD.eigenvalues i ≤ ∑ i ∈ Sp, hD.eigenvalues i := hdrop
    _ = ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) := (Finset.sum_coe_sort Sp _).symm
    _ ≤ (E.card : ℝ) + (Fintype.card V : ℝ) / 2 := by
        have hμpos : 0 ≤ (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E)) :=
          sum_nonneg fun i _ => le_of_lt (hμ i)
        have e2 : ((Fintype.card ↥Sp : ℝ) ≤ (Fintype.card V : ℝ)) := by
          exact_mod_cast hrcard
        have key : (2 : ℝ) * (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E))
            ≤ 2 * ((E.card : ℝ) + (Fintype.card V : ℝ) / 2) := by
          calc 2 * (∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E))
              ≤ ∑ i : ↥Sp, hD.eigenvalues (i : V ⊕ E) ^ 2
                + (Fintype.card ↥Sp : ℝ) := hsum1
            _ ≤ 2 * (E.card : ℝ) + (Fintype.card V : ℝ) := by linarith [hsq2, e2]
            _ = 2 * ((E.card : ℝ) + (Fintype.card V : ℝ) / 2) := by ring
        linarith [key, hμpos]

end Graph
end

end ConnectionGraph
