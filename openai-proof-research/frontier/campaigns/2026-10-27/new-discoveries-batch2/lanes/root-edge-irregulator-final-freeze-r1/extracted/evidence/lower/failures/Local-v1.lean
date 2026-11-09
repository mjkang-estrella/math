import Degrees
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator
open SimpleGraph
noncomputable section
attribute [local instance 10] Classical.propDecidable
 theorem filter_two {A : Type} [DecidableEq A] (p : A → Prop) [DecidablePred p]
    (a b : A) (hab : a ≠ b) :
    (({a,b} : Finset A).filter p).card = (if p a then 1 else 0)+(if p b then 1 else 0) := by
  by_cases ha : p a <;> by_cases hb : p b <;> simp [ha,hb,hab]
 theorem edge_reverse {t : ℕ} (i : Fin t) (k : Fin 8) :
    s((ends i k).2,(ends i k).1) = edge (i,k) := Sym2.eq_swap
 theorem degree_b {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 1) = db (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  simp only [neighbors,Fin.isValue,Matrix.cons_val_one]
  rw [filter_three]
  · simp only [db,bit,mask,edge,ends,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_succ,Fin.isValue,Sym2.eq_swap]
    split_ifs <;> simp_all
  all_goals simp [node]
 theorem degree_c {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 2) = dc (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  simp only [neighbors,Fin.isValue,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [filter_three]
  · simp only [dc,bit,mask,edge,ends,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_succ,Fin.isValue,Sym2.eq_swap]
    split_ifs <;> simp_all
  all_goals simp [node]
 theorem degree_d {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 3) = dd (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  simp only [neighbors,Fin.isValue,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [filter_two]
  · simp only [dd,bit,mask,edge,ends,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_succ,Fin.isValue,Sym2.eq_swap]
    split_ifs <;> simp_all
  simp [node]
 theorem degree_x {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 4) = dx (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  simp only [neighbors,Fin.isValue,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [filter_two]
  · simp only [dx,bit,mask,edge,ends,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_succ,Fin.isValue,Sym2.eq_swap]
    split_ifs <;> simp_all
  simp [node]
 theorem degree_y {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (Retained (graph t) S).degree (node i 5) = dy (mask S i) := by
  rw [← card_neighborFinset_eq_degree,retained_neighbors]
  simp only [neighbors,Fin.isValue,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [filter_two]
  · simp only [dy,bit,mask,edge,ends,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_succ,Fin.isValue,Sym2.eq_swap]
    split_ifs <;> simp_all
  simp [node,hub]
end
end EdgeIrregulator
