import Degrees
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace EdgeIrregulator
open SimpleGraph
noncomputable section
attribute [local instance 10] Classical.propDecidable
 theorem filter_two {A : Type} [DecidableEq A] (p : A → Prop) [DecidablePred p]
    (a b : A) (hab : a ≠ b) :
    (({a,b} : Finset A).filter p).card = (if p a then 1 else 0)+(if p b then 1 else 0) := by
  by_cases ha : p a <;> by_cases hb : p b <;> simp [Finset.filter_insert, Finset.filter_singleton,ha,hb,hab]
 theorem edge_reverse {t : ℕ} (i : Fin t) (k : Fin 8) :
    s((ends i k).2,(ends i k).1) = edge (i,k) := Sym2.eq_swap
 theorem degree_b {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 1) = db (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  change (({node i 0,node i 2,node i 3} : Finset (Vertex t)).filter (fun w => s(node i 1,w) ∉ S)).card = db (mask S i)
  rw [filter_three]
  · dsimp [db,bit,mask,edge,ends]
    simp only [Sym2.eq_swap]
    split_ifs <;> simp_all
  all_goals simp [node]
 theorem degree_c {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 2) = dc (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  change (({node i 0,node i 1,node i 4} : Finset (Vertex t)).filter (fun w => s(node i 2,w) ∉ S)).card = dc (mask S i)
  rw [filter_three]
  · dsimp [dc,bit,mask,edge,ends]
    simp only [Sym2.eq_swap]
    split_ifs <;> simp_all
  all_goals simp [node]
 theorem degree_d {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 3) = dd (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  change (({node i 0,node i 1} : Finset (Vertex t)).filter (fun w => s(node i 3,w) ∉ S)).card = dd (mask S i)
  rw [filter_two]
  · dsimp [dd,bit,mask,edge,ends]
    simp only [Sym2.eq_swap]
    split_ifs <;> simp_all
  simp [node]
 theorem degree_x {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 4) = dx (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  change (({node i 2,node i 5} : Finset (Vertex t)).filter (fun w => s(node i 4,w) ∉ S)).card = dx (mask S i)
  rw [filter_two]
  · dsimp [dx,bit,mask,edge,ends]
    simp only [Sym2.eq_swap]
    split_ifs <;> simp_all
  simp [node]
 theorem degree_y {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 5) = dy (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  change (({node i 4,hub t} : Finset (Vertex t)).filter (fun w => s(node i 5,w) ∉ S)).card = dy (mask S i)
  rw [filter_two]
  · dsimp [dy,bit,mask,edge,ends]
    simp only [Sym2.eq_swap]
    split_ifs <;> simp_all
  simp [node,hub]
end
end EdgeIrregulator
