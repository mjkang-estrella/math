import Mathlib

open Finset Matrix

namespace ConnectionGraph

noncomputable section

variable {V : Type*} [Fintype V] [LinearOrder V]

def ValidEdges (E : Finset (V × V)) : Prop := ∀ e ∈ E, e.1 < e.2

def edgePairs (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  univ.filter fun e => G.Adj e.1 e.2 ∧ e.1 < e.2

theorem edgePairs_valid (G : SimpleGraph V) [DecidableRel G.Adj] : ValidEdges (edgePairs G) := by
  intro e he
  exact (mem_filter.mp he).2.2

theorem adj_iff_edgePairs (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    G.Adj x y ↔ (x, y) ∈ edgePairs G ∨ (y, x) ∈ edgePairs G := by
  constructor
  · intro h
    rcases lt_or_gt_of_ne h.ne with hxy | hyx
    · exact Or.inl (mem_filter.mpr ⟨mem_univ _, h, hxy⟩)
    · exact Or.inr (mem_filter.mpr ⟨mem_univ _, h.symm, hyx⟩)
  · rintro (h | h)
    · exact (mem_filter.mp h).2.1
    · exact (mem_filter.mp h).2.1.symm

def unsignedIncidence (E : Finset (V × V)) : Matrix V E ℝ :=
  fun x e => (if x = e.val.1 then 1 else 0) + (if x = e.val.2 then 1 else 0)

def signedIncidence (E : Finset (V × V)) : Matrix V E ℝ :=
  fun x e => (if x = e.val.2 then 1 else 0) - (if x = e.val.1 then 1 else 0)

def degree (E : Finset (V × V)) (x : V) : ℝ := ∑ e, unsignedIncidence E x e

def signlessLaplacian (E : Finset (V × V)) : Matrix V V ℝ :=
  unsignedIncidence E * (unsignedIncidence E)ᵀ

def graphLaplacian (E : Finset (V × V)) : Matrix V V ℝ :=
  signedIncidence E * (signedIncidence E)ᵀ

def simplex (E : Finset (V × V)) : V ⊕ E → Finset V
  | Sum.inl x => {x}
  | Sum.inr e => {e.val.1, e.val.2}

def connectionMatrix (E : Finset (V × V)) : Matrix (V ⊕ E) (V ⊕ E) ℝ :=
  fun a b => if (simplex E a ∩ simplex E b).Nonempty then 1 else 0

def boundaryMatrix (E : Finset (V × V)) : Matrix (V ⊕ E) (V ⊕ E) ℝ :=
  fromBlocks 0 (signedIncidence E) 0 0

def diracMatrix (E : Finset (V × V)) : Matrix (V ⊕ E) (V ⊕ E) ℝ :=
  boundaryMatrix E + (boundaryMatrix E)ᵀ

def blockConnection (E : Finset (V × V)) : Matrix (V ⊕ E) (V ⊕ E) ℝ :=
  fromBlocks 1 (unsignedIncidence E) (unsignedIncidence E)ᵀ
    ((unsignedIncidence E)ᵀ * unsignedIncidence E - 1)

omit [Fintype V] in
theorem unsigned_nonneg (E : Finset (V × V)) (x : V) (e : E) :
    0 ≤ unsignedIncidence E x e := by
  unfold unsignedIncidence
  positivity

omit [Fintype V] in
theorem degree_nonneg (E : Finset (V × V)) (x : V) : 0 ≤ degree E x := by
  apply sum_nonneg
  intro e _
  exact unsigned_nonneg E x e

theorem unsigned_column_sum (E : Finset (V × V)) (e : E) :
    ∑ x, unsignedIncidence E x e = 2 := by
  norm_num [unsignedIncidence, sum_add_distrib]

theorem degree_sum (E : Finset (V × V)) : ∑ x, degree E x = 2 * (E.card : ℝ) := by
  simp only [degree, unsignedIncidence]
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib]
  ring

omit [Fintype V] in
theorem edge_ne {E : Finset (V × V)} (hE : ValidEdges E) (e : E) : e.val.1 ≠ e.val.2 :=
  ne_of_lt (hE e.val e.property)

omit [Fintype V] in
theorem unsigned_square {E : Finset (V × V)} (hE : ValidEdges E) (x : V) (e : E) :
    unsignedIncidence E x e ^ 2 = unsignedIncidence E x e := by
  have hne := edge_ne hE e
  by_cases h1 : x = e.val.1 <;> by_cases h2 : x = e.val.2 <;>
    simp_all [unsignedIncidence]

omit [Fintype V] in
theorem signless_diagonal {E : Finset (V × V)} (hE : ValidEdges E) (x : V) :
    signlessLaplacian E x x = degree E x := by
  simp only [signlessLaplacian, mul_apply, transpose_apply, degree]
  apply sum_congr rfl
  intro e _
  simpa only [pow_two] using unsigned_square hE x e

theorem unsigned_transpose_mulVec (E : Finset (V × V)) (z : V → ℝ) (e : E) :
    ((unsignedIncidence E)ᵀ *ᵥ z) e = z e.val.1 + z e.val.2 := by
  simp [mulVec, dotProduct, transpose_apply, unsignedIncidence, add_mul, sum_add_distrib]

theorem signed_transpose_mulVec (E : Finset (V × V)) (z : V → ℝ) (e : E) :
    ((signedIncidence E)ᵀ *ᵥ z) e = z e.val.2 - z e.val.1 := by
  simp [mulVec, dotProduct, transpose_apply, signedIncidence, sub_mul, sum_sub_distrib]

omit [Fintype V] in
theorem dirac_block (E : Finset (V × V)) :
    diracMatrix E = fromBlocks 0 (signedIncidence E) (signedIncidence E)ᵀ 0 := by
  ext (a | a) (b | b) <;> simp [diracMatrix, boundaryMatrix]

omit [Fintype V] in
theorem connection_hermitian (E : Finset (V × V)) : (connectionMatrix E).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [connectionMatrix, inter_comm]

omit [Fintype V] in
theorem dirac_hermitian (E : Finset (V × V)) : (diracMatrix E).IsHermitian := by
  simp [diracMatrix, Matrix.IsHermitian, add_comm]

theorem signed_energy (E : Finset (V × V)) (z : V → ℝ) :
    z ⬝ᵥ (graphLaplacian E *ᵥ z) = ∑ e : E, (z e.val.2 - z e.val.1) ^ 2 := by
  rw [graphLaplacian, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp only [dotProduct, signed_transpose_mulVec, pow_two]

theorem unsigned_energy (E : Finset (V × V)) (z : V → ℝ) :
    z ⬝ᵥ (signlessLaplacian E *ᵥ z) = ∑ e : E, (z e.val.1 + z e.val.2) ^ 2 := by
  rw [signlessLaplacian, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp only [dotProduct, unsigned_transpose_mulVec, pow_two]

theorem degree_energy (E : Finset (V × V)) (z : V → ℝ) :
    (∑ x, degree E x * z x ^ 2) = ∑ e : E, (z e.val.1 ^ 2 + z e.val.2 ^ 2) := by
  simp only [degree, unsignedIncidence, Finset.sum_mul, add_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro e _
  simp [sum_add_distrib]

theorem graph_degree_quadratic_bound (E : Finset (V × V)) (z : V → ℝ) :
    z ⬝ᵥ (graphLaplacian E *ᵥ z) ≤ 2 * ∑ x, degree E x * z x ^ 2 := by
  rw [signed_energy, degree_energy, Finset.mul_sum]
  apply sum_le_sum
  intro e _
  nlinarith [sq_nonneg (z e.val.1 + z e.val.2)]

theorem signless_nonneg (E : Finset (V × V)) (z : V → ℝ) :
    0 ≤ z ⬝ᵥ (signlessLaplacian E *ᵥ z) := by
  rw [unsigned_energy]
  exact sum_nonneg (fun _ _ => sq_nonneg _)

theorem laplacian_nonneg (E : Finset (V × V)) (z : V → ℝ) :
    0 ≤ z ⬝ᵥ (graphLaplacian E *ᵥ z) := by
  rw [signed_energy]
  exact sum_nonneg (fun _ _ => sq_nonneg _)


end
end ConnectionGraph
