import ConnectionLift
import IncidenceBlocks

open Finset Matrix
open scoped RealInnerProductSpace

namespace ConnectionGraph
noncomputable section

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem liftedBlock_shift_posSemidef (U : Matrix n m ℝ) :
    (liftedBlock U + 1).PosSemidef := by
  let B : Matrix (n ⊕ m) (n ⊕ m) ℝ := fromBlocks 1 U 0 0
  let J : Matrix (n ⊕ m) (n ⊕ m) ℝ := fromBlocks 1 0 0 0
  have heq : liftedBlock U + 1 = Bᴴ * B + Jᴴ * J := by
    simp only [B, J, liftedBlock, fromBlocks_conjTranspose, conjTranspose_one,
      conjTranspose_zero, fromBlocks_multiply, mul_one, mul_zero, add_zero]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self B).add
    (Matrix.posSemidef_conjTranspose_mul_self J)

theorem liftedBlock_eigenvalues_lower (U : Matrix n m ℝ) (i : n ⊕ m) :
    -1 ≤ (liftedBlock_hermitian U).eigenvalues i := by
  let hL := liftedBlock_hermitian U
  let x := hL.eigenvectorBasis i
  have hp := (liftedBlock_shift_posSemidef U).dotProduct_mulVec_nonneg x.ofLp
  have he := hL.mulVec_eigenvectorBasis i
  change liftedBlock U *ᵥ x.ofLp = hL.eigenvalues i • x.ofLp at he
  have hx : x.ofLp ⬝ᵥ x.ofLp = 1 := by
    have hn := hL.eigenvectorBasis.inner_eq_one i
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hn
  simp only [star_trivial, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
    he, dotProduct_smul, smul_eq_mul, hx, mul_one] at hp
  linarith

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem edge_card_le_choose_two {E : Finset (V × V)} (hE : ValidEdges E) :
    E.card ≤ (Fintype.card V).choose 2 := by
  calc
    E.card ≤ ((univ ×ˢ univ : Finset (V × V)).filter fun e => e.1 < e.2).card := by
      apply card_le_card
      intro e he
      exact mem_filter.mpr ⟨by simp, hE e he⟩
    _ = _ := by rw [card_product_filter_lt, card_univ]

theorem edge_card_real_bound [Nonempty V] {E : Finset (V × V)} (hE : ValidEdges E) :
    2 * (E.card : ℝ) + 1 ≤ (Fintype.card V : ℝ) ^ 2 := by
  have hv : 1 ≤ Fintype.card V := Fintype.card_pos
  have hb := edge_card_le_choose_two hE
  have hbr : (E.card : ℝ) ≤ ((Fintype.card V).choose 2 : ℝ) := by exact_mod_cast hb
  rw [Nat.cast_choose_two] at hbr
  have hvr : 1 ≤ (Fintype.card V : ℝ) := by exact_mod_cast hv
  nlinarith

omit [LinearOrder V] in
theorem positive_branch_total_lower [Nonempty V] (q : V → ℝ)
    (hq : ∀ i, 0 ≤ q i) {M : ℝ} (hM : 0 ≤ M) (htrace : ∑ i, q i = 2 * M)
    (hcard : 2 * M + 1 ≤ (Fintype.card V : ℝ) ^ 2) :
    2 * M + 1 ≤ ∑ i, positiveBranch (q i) := by
  let g : ℝ := ∑ i, (positiveBranch (q i))⁻¹
  have hg : 0 ≤ g := sum_nonneg fun i _ => inv_nonneg.mpr (positiveBranch_pos (hq i)).le
  have hs : (∑ i, positiveBranch (q i)) = 2 * M + g := by
    calc
      _ = ∑ i, (q i + (positiveBranch (q i))⁻¹) :=
        sum_congr rfl fun i _ => positiveBranch_eq_add_inv (hq i)
      _ = _ := by rw [sum_add_distrib, htrace]
  have hspos : 0 < ∑ i, positiveBranch (q i) :=
    sum_pos (fun i _ => positiveBranch_pos (hq i)) univ_nonempty
  have hc := sq_sum_div_le_sum_sq_div (univ : Finset V) (fun _ => (1 : ℝ))
    (g := fun i => positiveBranch (q i)) (fun i _ => positiveBranch_pos (hq i))
  simp only [sum_const, nsmul_eq_mul, mul_one, one_pow, one_div] at hc
  have hc' : (Fintype.card V : ℝ) ^ 2 ≤ g * (2 * M + g) := by
    have ht := (div_le_iff₀ hspos).mp hc
    rwa [hs] at ht
  have hg1 : 1 ≤ g := by
    by_contra h
    have hlt : g < 1 := lt_of_not_ge h
    have hmul := mul_nonneg hM (sub_nonneg.mpr hlt.le)
    nlinarith [mul_pos (sub_pos.mpr hlt) (show 0 < 1 + g by linarith)]
  rw [hs]
  linarith

theorem graph_signless_trace {E : Finset (V × V)} (hE : ValidEdges E) :
    (∑ i, (gramHermitian (unsignedIncidence E)).eigenvalues i) = 2 * (E.card : ℝ) := by
  have ht : (signlessLaplacian E).trace =
      ∑ i, (gramHermitian (unsignedIncidence E)).eigenvalues i := by
    simpa [signlessLaplacian] using
      (gramHermitian (unsignedIncidence E)).trace_eq_sum_eigenvalues
  rw [← ht]
  change (∑ i, signlessLaplacian E i i) = _
  simp_rw [signless_diagonal hE]
  exact degree_sum E

theorem graph_connection_vertex_sum_lower [Nonempty V] {E : Finset (V × V)}
    (hE : ValidEdges E) :
    2 * (E.card : ℝ) + 1 ≤ spectralTopSum (connection_hermitian E) (Fintype.card V) := by
  let U := unsignedIncidence E
  have hsum := positive_branch_total_lower ((gramHermitian U).eigenvalues)
    (gram_eigenvalues_nonneg U) (show 0 ≤ (E.card : ℝ) by positivity)
    (graph_signless_trace hE) (edge_card_real_bound hE)
  have hl := selected_positive_branches_le U (univ : Finset V)
  rw [card_univ] at hl
  have heq : liftedBlock U = connectionMatrix E := (connection_eq_blocks hE).symm
  have hl' : (∑ i, positiveBranch ((gramHermitian U).eigenvalues i)) ≤
      spectralTopSum (connection_hermitian E) (Fintype.card V) := by
    simpa only [heq] using hl
  exact hsum.trans hl'

omit [Fintype V] in
theorem connection_diagonal (E : Finset (V × V)) (i : V ⊕ E) :
    connectionMatrix E i i = 1 := by
  cases i <;> simp [connectionMatrix, simplex]

theorem graph_connection_sum_ge_index (E : Finset (V × V)) {k : ℕ}
    (hk : k ≤ Fintype.card V + E.card) :
    (k : ℝ) ≤ spectralTopSum (connection_hermitian E) k := by
  have hk' : k ≤ Fintype.card (V ⊕ E) := by simpa using hk
  have hd := spectralTopSum_diagonal_le (connection_hermitian E) hk'
  simp only [connection_diagonal, sortedTopSum_const _ hk', mul_one] at hd
  exact hd

theorem graph_connection_growth {E : Finset (V × V)} (hE : ValidEdges E)
    {k : ℕ} (hv : Fintype.card V ≤ k) (hk : k ≤ Fintype.card V + E.card) :
    spectralTopSum (connection_hermitian E) (Fintype.card V) -
      (k - Fintype.card V : ℕ) ≤ spectralTopSum (connection_hermitian E) k := by
  have hk' : k ≤ Fintype.card (V ⊕ E) := by simpa using hk
  have hlow : ∀ i, -1 ≤ (connection_hermitian E).eigenvalues i := by
    intro i
    have h := liftedBlock_eigenvalues_lower (unsignedIncidence E) i
    have heq : liftedBlock (unsignedIncidence E) = connectionMatrix E :=
      (connection_eq_blocks hE).symm
    simpa only [heq] using h
  have ht := sortedTopSum_growth_lower (connection_hermitian E).eigenvalues hv hk' hlow
  simpa only [spectralTopSum, mul_neg_one, sub_eq_add_neg] using ht

theorem graph_high_connection_bound [Nonempty V] {E : Finset (V × V)}
    (hE : ValidEdges E) {k : ℕ} (hv : Fintype.card V ≤ k)
    (hk : k ≤ Fintype.card V + E.card) :
    (E.card : ℝ) + (Fintype.card V : ℝ) / 2 + 1 / 2 ≤
      spectralTopSum (connection_hermitian E) k := by
  have hvertex := graph_connection_vertex_sum_lower hE
  have hgrowth := graph_connection_growth hE hv hk
  have hindex := graph_connection_sum_ge_index E hk
  rw [Nat.cast_sub hv] at hgrowth
  linarith

end
end ConnectionGraph
