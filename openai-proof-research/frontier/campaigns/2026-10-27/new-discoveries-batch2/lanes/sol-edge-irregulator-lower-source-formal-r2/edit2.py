from pathlib import Path
p=Path(__file__).parent/'component/formal/Lower.lean'
s=p.read_text().replace('import Mathlib.Algebra.BigOperators.Fin','import Mathlib.Algebra.BigOperators.Fin\nimport Mathlib.Algebra.Order.BigOperators.Group.Finset')
s=s.replace('  exact ⟨he, by simpa [mask,edge] using h⟩','  rw [Retained,deleteEdges_adj]\n  refine ⟨he,?_⟩\n  by_cases hm : edge (i,k) ∈ S\n  · simp [mask,hm] at h\n  · exact hm')
s=s.replace('  · simpa only [ends,Matrix.cons_val_zero,degree_a,degree_b] using hh 0 hk','  · have hx := hh 0 hk\n    change (Retained (graph t) S).degree (node i 0) ≠ (Retained (graph t) S).degree (node i 1) at hx\n    simpa only [degree_a,degree_b] using hx')
s=s.replace('rw [Finset.card_eq_sum_ones,Finset.sum_filter]','rw [blockDeleted,Finset.card_eq_sum_ones,Finset.sum_filter]')
s=s.replace('rw [heq,Finset.card_image_of_injective _ (edge_injective t)]','conv_lhs => rw [heq,Finset.card_image_of_injective _ (edge_injective t)]')
s=s.replace('Finset.univ_product,\n    Finset.sum_product','Fintype.sum_prod_type')
p.write_text(s)
