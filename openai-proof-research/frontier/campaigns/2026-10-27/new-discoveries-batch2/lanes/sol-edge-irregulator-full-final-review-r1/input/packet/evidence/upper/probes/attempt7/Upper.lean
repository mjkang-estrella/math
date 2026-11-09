import UpperDegrees
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace EdgeIrregulator.Upper
open SimpleGraph
noncomputable section
attribute [local instance 10] Classical.propDecidable
theorem hub_neighbors (t : ℕ) :
    (Retained (graph t) (deletion t)).neighborFinset (hub t) =
      Finset.univ.image (fun i : Fin t => node i 5) := by
  ext w
  classical
  simp only [mem_neighborFinset, Retained, deleteEdges_adj, Finset.mem_coe]
  cases w with
  | inl u => cases u; simp [graph, graphAdj, hub, node]
  | inr p =>
    rcases p with ⟨i,v⟩
    have h7 := edge_mem_deletion i 7
    simp only [edge, ends] at h7
    fin_cases v <;> simp_all [graph, graphAdj, hub, node, Sym2.eq_swap]
theorem hub_degree (t : ℕ) : (Retained (graph t) (deletion t)).degree (hub t) = t := by
  rw [← card_neighborFinset_eq_degree, hub_neighbors,
    Finset.card_image_of_injective _ (show Function.Injective (fun i : Fin t => node i 5) by
      intro i j h; simpa [node] using h)]
  simp
-- Every retained edge is one of ac,bc,bd,cx,yh, in either orientation.
theorem retained_edge_classification {t : ℕ} (u v : Vertex t)
    (h : (Retained (graph t) (deletion t)).Adj u v) :
    ∃ i : Fin t, ∃ k : Fin 8, (k=1 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=7) ∧
      (u=(ends i k).1 ∧ v=(ends i k).2 ∨ u=(ends i k).2 ∧ v=(ends i k).1) := by
  have hh : (graph t).Adj u v ∧ s(u,v) ∉ deletion t := by
    simpa only [Retained, deleteEdges_adj, Finset.mem_coe] using h
  have hg := hh.1
  obtain ⟨⟨i,k⟩,he⟩ := edge_surjective s(u,v) (by simpa using hg)
  have hn : edge (i,k) ∉ deletion t := by
    rw [he]
    exact hh.2
  have hk := (edge_mem_deletion i k).not.mp hn
  refine ⟨i,k,?_,?_⟩
  · fin_cases k <;> simp_all
  · have he' := Sym2.eq_iff.mp he
    rcases he' with h | h
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · exact Or.inr ⟨h.2.symm,h.1.symm⟩
theorem witness_valid (t : ℕ) (ht : 2 ≤ t) : Valid (graph t) (deletion t) := by
  refine ⟨deletion_subset t,?_⟩
  intro u v h
  obtain ⟨i,k,hk,hor⟩ := retained_edge_classification u v h
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    dsimp only [ends, Matrix.cons_val_zero, Matrix.cons_val_succ, Prod.fst, Prod.snd] <;>
    simp only [private_degree, hub_degree] <;> norm_num <;>
    omega
theorem minimum_upper (t : ℕ) (ht : 2 ≤ t) : minimum (graph t) ≤ 3*t := by
  simpa [deletion_card] using minimum_le (graph t) (deletion t) (witness_valid t ht)
end
end EdgeIrregulator.Upper
