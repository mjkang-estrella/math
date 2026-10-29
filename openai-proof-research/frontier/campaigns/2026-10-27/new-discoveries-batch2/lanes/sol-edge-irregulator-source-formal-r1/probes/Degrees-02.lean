import Edges
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator
open SimpleGraph
noncomputable section
attribute [local instance 10] Classical.propDecidable
def neighbors {t : ℕ} (i : Fin t) (v : Fin 6) : Finset (Vertex t) :=
  ![{node i 1,node i 2,node i 3},{node i 0,node i 2,node i 3},
    {node i 0,node i 1,node i 4},{node i 0,node i 1},
    {node i 2,node i 5},{node i 4,hub t}] v
theorem retained_neighbors {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) (v : Fin 6) :
    (Retained (graph t) S).neighborFinset (node i v) =
    (neighbors i v).filter (fun w => s(node i v,w) ∉ S) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
  simp only [Retained,SimpleGraph.deleteEdges_adj,Finset.mem_coe]
  congr 1
  cases w with
  | inl a => cases a; fin_cases v <;> simp [graph,graphAdj,node,hub,neighbors]
  | inr a =>
    rcases a with ⟨j,u⟩
    fin_cases v <;> fin_cases u <;>
      simp [graph,graphAdj,node,hub,neighbors,localAdj,eq_comm]
def mask {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) : Fin 8 → Bool :=
  fun k => decide (edge (i,k) ∉ S)
theorem degree_a {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 0) = da (mask S i) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,retained_neighbors]
  simp only [neighbors,Fin.isValue,Matrix.cons_val_zero]
  simp [da,bit,mask,edge,ends,node,Finset.filter_insert,Finset.filter_singleton]
end
end EdgeIrregulator
