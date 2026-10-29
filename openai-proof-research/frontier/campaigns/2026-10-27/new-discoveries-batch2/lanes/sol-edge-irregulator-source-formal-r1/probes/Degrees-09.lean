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
  cases w with
  | inl a => cases a; fin_cases v <;> simp [graph,graphAdj,node,hub,neighbors]
  | inr a =>
    rcases a with ⟨j,u⟩
    fin_cases v <;> fin_cases u <;>
      simp [graph,graphAdj,node,hub,neighbors,localAdj,eq_comm]
def mask {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) : Fin 8 → Bool :=
  fun k => if edge (i,k) ∈ S then false else true
theorem filter_three {A : Type} [DecidableEq A] (p : A → Prop) [DecidablePred p]
    (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (({a,b,c} : Finset A).filter p).card = (if p a then 1 else 0)+(if p b then 1 else 0)+(if p c then 1 else 0) := by
  have hf : ({a,b,c} : Finset A).filter p = (if p a then {a} else ∅) ∪
      (if p b then {b} else ∅) ∪ (if p c then {c} else ∅) := by
    ext x
    by_cases ha : p a <;> by_cases hb : p b <;> by_cases hc : p c <;>
      simp_all only [ite_eq_left,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_union] <;> aesop
  rw [hf]
  split_ifs <;> simp_all [Finset.card_insert_of_notMem]
theorem degree_a {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 0) = da (mask S i) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,retained_neighbors]
  simp only [neighbors,Fin.isValue,Matrix.cons_val_zero]
  rw [filter_three]
  · unfold da bit mask
    split_ifs <;> simp_all [edge,ends]
  all_goals simp [node]
theorem degree_b {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 1) = db (mask S i) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,retained_neighbors]
  dsimp [neighbors]
  rw [filter_three]
  · unfold db bit mask
    split_ifs <;> simp_all [edge,ends,Sym2.eq_swap]
  all_goals simp [node]
theorem degree_c {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 2) = dc (mask S i) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,retained_neighbors]
  dsimp [neighbors]
  rw [filter_three]
  · unfold dc bit mask
    split_ifs <;> simp_all [edge,ends,Sym2.eq_swap]
  all_goals simp [node]
theorem filter_two {A : Type} [DecidableEq A] (p : A → Prop) [DecidablePred p]
    (a b : A) (hab : a ≠ b) :
    (({a,b} : Finset A).filter p).card = (if p a then 1 else 0)+(if p b then 1 else 0) := by
  have hf : ({a,b} : Finset A).filter p = (if p a then {a} else ∅) ∪
      (if p b then {b} else ∅) := by
    ext x
    by_cases ha : p a <;> by_cases hb : p b <;>
      simp_all only [ite_eq_left,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_union] <;> aesop
  rw [hf]
  split_ifs <;> simp_all [Finset.card_insert_of_notMem]
theorem degree_d {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 3) = dd (mask S i) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,retained_neighbors]
  dsimp [neighbors]
  rw [filter_two]
  · unfold dd bit mask
    split_ifs <;> simp_all [edge,ends,Sym2.eq_swap]
  all_goals simp [node]
theorem degree_x {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 4) = dx (mask S i) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,retained_neighbors]
  dsimp [neighbors]
  rw [filter_two]
  · unfold dx bit mask
    split_ifs <;> simp_all [edge,ends,Sym2.eq_swap]
  all_goals simp [node]
theorem degree_y {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 5) = dy (mask S i) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,retained_neighbors]
  dsimp [neighbors]
  rw [filter_two]
  · unfold dy bit mask
    split_ifs <;> simp_all [edge,ends,Sym2.eq_swap]
  all_goals simp [node,hub]
end
end EdgeIrregulator
