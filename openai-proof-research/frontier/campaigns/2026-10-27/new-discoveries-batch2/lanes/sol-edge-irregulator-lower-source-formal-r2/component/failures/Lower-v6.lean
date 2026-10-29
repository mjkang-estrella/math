import Local
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace EdgeIrregulator
open SimpleGraph
open scoped BigOperators
noncomputable section
attribute [local instance 10] Classical.propDecidable
 theorem mask_adj {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) (k : Fin 8)
    (h : mask S i k = true) : (Retained (graph t) S).Adj (ends i k).1 (ends i k).2 := by
  have he := edge_is_edge (i,k)
  rw [mem_edgeFinset] at he
  rw [Retained,deleteEdges_adj]
  refine ⟨he,?_⟩
  by_cases hm : edge (i,k) ∈ S
  · simp [mask,hm] at h
  · exact hm
 theorem valid_diamond {t : ℕ} (S : Finset (Sym2 (Vertex t))) (h : Valid (graph t) S)
    (i : Fin t) : DiamondOK (mask S i) := by
  have hh := fun k hk => h.2 _ _ (mask_adj S i k hk)
  unfold DiamondOK
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals intro hk
  · have hx := hh 0 hk
    change (Retained (graph t) S).degree (node i 0) ≠ (Retained (graph t) S).degree (node i 1) at hx
    simpa only [degree_a,degree_b] using hx
  · have := hh 1 hk
    change (Retained (graph t) S).degree (node i 0) ≠ (Retained (graph t) S).degree (node i 2) at this
    simpa only [degree_a,degree_c] using this
  · have := hh 2 hk
    change (Retained (graph t) S).degree (node i 0) ≠ (Retained (graph t) S).degree (node i 3) at this
    simpa only [degree_a,degree_d] using this
  · have := hh 3 hk
    change (Retained (graph t) S).degree (node i 1) ≠ (Retained (graph t) S).degree (node i 2) at this
    simpa only [degree_b,degree_c] using this
  · have := hh 4 hk
    change (Retained (graph t) S).degree (node i 1) ≠ (Retained (graph t) S).degree (node i 3) at this
    simpa only [degree_b,degree_d] using this
 theorem valid_xy {t : ℕ} (S : Finset (Sym2 (Vertex t))) (h : Valid (graph t) S)
    (i : Fin t) : mask S i 6 = true → dx (mask S i) ≠ dy (mask S i) := by
  intro hk
  have hh := h.2 _ _ (mask_adj S i 6 hk)
  change (Retained (graph t) S).degree (node i 4) ≠ (Retained (graph t) S).degree (node i 5) at hh
  simpa only [degree_x,degree_y] using hh
 def blockDeleted {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) : Finset (Fin 8) :=
  Finset.univ.filter (fun k => edge (i,k) ∈ S)
 theorem block_cost {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (blockDeleted S i).card = diamondCost (mask S i) + pathCost (mask S i) := by
  rw [blockDeleted,Finset.card_eq_sum_ones,Finset.sum_filter]
  change (∑ k : Fin 8, if edge (i,k) ∈ S then 1 else 0) = _
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,
    Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero,Finset.sum_empty,Nat.add_zero]
  have hb : ∀ k, 1 - bit (mask S i) k = if edge (i,k) ∈ S then 1 else 0 := by
    intro k
    by_cases hk : edge (i,k) ∈ S <;> simp [bit,mask,hk]
  simp only [diamondCost,pathCost,hb]
  ac_rfl
 theorem deleted_card_sum {t : ℕ} (S : Finset (Sym2 (Vertex t))) (h : S ⊆ (graph t).edgeFinset) :
    S.card = ∑ i : Fin t, (blockDeleted S i).card := by
  let T := Finset.univ.filter (fun ik : Fin t × Fin 8 => edge ik ∈ S)
  have heq : S = T.image edge := by
    ext e
    constructor
    · intro he
      obtain ⟨ik,rfl⟩ := edge_surjective e (h he)
      exact Finset.mem_image.mpr ⟨ik,by simpa [T],rfl⟩
    · intro he
      obtain ⟨ik,hi,rfl⟩ := Finset.mem_image.mp he
      simpa [T] using hi
  conv_lhs => rw [heq,Finset.card_image_of_injective _ (edge_injective t)]
  simp only [T,Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type,blockDeleted]
 theorem deletion_card_lower (t : ℕ) (S : Finset (Sym2 (Vertex t))) (h : Valid (graph t) S) :
    3*t ≤ S.card := by
  rw [deleted_card_sum S h.1]
  calc
    3*t = ∑ _i : Fin t, 3 := by simp [Nat.mul_comm]
    _ ≤ ∑ i : Fin t, (blockDeleted S i).card := by
      apply Finset.sum_le_sum
      intro i _
      rw [block_cost]
      exact block_boundary_certificate _ (valid_diamond S h i) (valid_xy S h i)
 theorem minimum_lower (t : ℕ) : 3*t ≤ minimum (graph t) := by
  obtain ⟨S,hS,hc⟩ := minimum_attained (graph t)
  simpa [hc] using deletion_card_lower t S hS
end
end EdgeIrregulator
