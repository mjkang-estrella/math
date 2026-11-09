import UpperWitness
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator.Upper
open SimpleGraph
noncomputable section
attribute [local instance 10] Classical.propDecidable
def keptNeighbors {t : ℕ} (i : Fin t) (v : Fin 6) : Finset (Vertex t) :=
  ![{node i 2},{node i 2,node i 3},{node i 0,node i 1,node i 4},
    {node i 1},{node i 2},{hub t}] v
theorem private_neighbors {t : ℕ} (i : Fin t) (v : Fin 6) :
    (Retained (graph t) (deletion t)).neighborFinset (node i v) = keptNeighbors i v := by
  have h0 := edge_mem_deletion i 0
  have h1 := edge_mem_deletion i 1
  have h2 := edge_mem_deletion i 2
  have h3 := edge_mem_deletion i 3
  have h4 := edge_mem_deletion i 4
  have h5 := edge_mem_deletion i 5
  have h6 := edge_mem_deletion i 6
  have h7 := edge_mem_deletion i 7
  simp only [edge, ends, Matrix.cons_val_zero] at h0 h1 h2 h3 h4 h5 h6 h7
  have hs0 := edge_mem_deletion i 0
  simp only [edge, ends, Matrix.cons_val_zero] at hs0
  rw [Sym2.eq_swap] at hs0
  have hs1 := edge_mem_deletion i 1
  simp only [edge, ends, Matrix.cons_val_zero] at hs1
  rw [Sym2.eq_swap] at hs1
  have hs2 := edge_mem_deletion i 2
  simp only [edge, ends, Matrix.cons_val_zero] at hs2
  rw [Sym2.eq_swap] at hs2
  have hs3 := edge_mem_deletion i 3
  simp only [edge, ends, Matrix.cons_val_zero] at hs3
  rw [Sym2.eq_swap] at hs3
  have hs4 := edge_mem_deletion i 4
  simp only [edge, ends, Matrix.cons_val_zero] at hs4
  rw [Sym2.eq_swap] at hs4
  have hs5 := edge_mem_deletion i 5
  simp only [edge, ends, Matrix.cons_val_zero] at hs5
  rw [Sym2.eq_swap] at hs5
  have hs6 := edge_mem_deletion i 6
  simp only [edge, ends, Matrix.cons_val_zero] at hs6
  rw [Sym2.eq_swap] at hs6
  have hs7 := edge_mem_deletion i 7
  simp only [edge, ends, Matrix.cons_val_zero] at hs7
  rw [Sym2.eq_swap] at hs7
  rw [retained_neighbors]
  fin_cases v <;>
    simp_all [neighbors, keptNeighbors, Finset.filter_insert, Finset.filter_singleton]
theorem private_degree {t : ℕ} (i : Fin t) (v : Fin 6) :
    (Retained (graph t) (deletion t)).degree (node i v) = ![1,2,3,1,1,1] v := by
  rw [← card_neighborFinset_eq_degree, private_neighbors]
  fin_cases v <;> simp [keptNeighbors, node, hub]
end
end EdgeIrregulator.Upper
