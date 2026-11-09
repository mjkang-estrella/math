import Lower
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator
open scoped BigOperators
noncomputable section
attribute [local instance 10] Classical.propDecidable
 def chargedEdges {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t)
    (q : Fin 8 → Prop) : Finset (Sym2 (Vertex t)) :=
  ((blockDeleted S i).filter q).image (fun k => edge (i,k))
 theorem chargedEdges_card {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t)
    (q : Fin 8 → Prop) : (chargedEdges S i q).card = ((blockDeleted S i).filter q).card := by
  apply Finset.card_image_of_injective
  intro a b h
  exact congrArg Prod.snd (edge_injective t h)
 theorem split_cost_bits : ∀ r : Fin 8 → Bool,
    (Finset.univ.filter (fun k => r k = false ∧ k.val < 5)).card = diamondCost r ∧
    (Finset.univ.filter (fun k => r k = false ∧ 5 ≤ k.val)).card = pathCost r := by
  decide +kernel
 theorem actual_diamond_cost {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (chargedEdges S i (fun k => k.val < 5)).card = diamondCost (mask S i) := by
  rw [chargedEdges_card,← (split_cost_bits (mask S i)).1]
  congr 1
  ext k
  by_cases hk : edge (i,k) ∈ S <;> simp [blockDeleted,mask,hk]
 theorem actual_path_cost {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (chargedEdges S i (fun k => 5 ≤ k.val)).card = pathCost (mask S i) := by
  rw [chargedEdges_card,← (split_cost_bits (mask S i)).2]
  congr 1
  ext k
  by_cases hk : edge (i,k) ∈ S <;> simp [blockDeleted,mask,hk]
 theorem charged_subset {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t)
    (q : Fin 8 → Prop) : chargedEdges S i q ⊆ S := by
  intro e he
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp he
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
 theorem charged_blocks_disjoint {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i j : Fin t)
    (hij : i ≠ j) (q r : Fin 8 → Prop) :
    Disjoint (chargedEdges S i q) (chargedEdges S j r) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp he
  obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hf
  exact hij (congrArg Prod.fst (edge_injective t (hk.trans hl.symm)))
 theorem charged_parts_disjoint {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    Disjoint (chargedEdges S i (fun k => k.val < 5)) (chargedEdges S i (fun k => 5 ≤ k.val)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp he
  obtain ⟨l,hl,hf⟩ := Finset.mem_image.mp hf
  have hkl := congrArg Prod.snd (edge_injective t (he.trans hf.symm))
  have hk1 := (@Finset.mem_filter (Fin 8) (fun k => k.val < 5) (fun k => Classical.propDecidable _) (blockDeleted S i) k).mp hk |>.2
  have hl1 := (@Finset.mem_filter (Fin 8) (fun k => 5 ≤ k.val) (fun k => Classical.propDecidable _) (blockDeleted S i) l).mp hl |>.2
  change k = l at hkl
  subst l
  omega
 theorem actual_deleted_sum {t : ℕ} (S : Finset (Sym2 (Vertex t))) (h : Valid (graph t) S) :
    S.card = ∑ i : Fin t, ((chargedEdges S i (fun k => k.val < 5)).card +
      (chargedEdges S i (fun k => 5 ≤ k.val)).card) := by
  rw [deleted_card_sum S h.1]
  apply Finset.sum_congr rfl
  intro i _
  rw [actual_diamond_cost,actual_path_cost,block_cost]
end
end EdgeIrregulator
