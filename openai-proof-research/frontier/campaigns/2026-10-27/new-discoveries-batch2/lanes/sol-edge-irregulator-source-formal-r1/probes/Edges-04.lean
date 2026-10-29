import Gadget
import Mathlib.Data.Fin.VecNotation
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
def ends {t : ℕ} (i : Fin t) (k : Fin 8) : Vertex t × Vertex t :=
  ![(node i 0,node i 1),(node i 0,node i 2),(node i 0,node i 3),
    (node i 1,node i 2),(node i 1,node i 3),(node i 2,node i 4),
    (node i 4,node i 5),(node i 5,hub t)] k
def edge {t : ℕ} (ik : Fin t × Fin 8) : Sym2 (Vertex t) :=
  s((ends ik.1 ik.2).1,(ends ik.1 ik.2).2)
theorem edge_injective (t : ℕ) : Function.Injective (@edge t) := by
  rintro ⟨i,k⟩ ⟨j,l⟩ h
  fin_cases k <;> fin_cases l <;>
    simp_all [edge, ends, node, hub]
theorem edge_is_edge {t : ℕ} (ik : Fin t × Fin 8) : edge ik ∈ (graph t).edgeFinset := by
  rcases ik with ⟨i,k⟩
  rw [SimpleGraph.mem_edgeFinset]
  fin_cases k <;> simp [edge,ends,graph,graphAdj,node,hub,localAdj]
theorem edge_surjective {t : ℕ} (e : Sym2 (Vertex t))
    (he : e ∈ (graph t).edgeFinset) : ∃ ik, edge ik = e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have ha : (graph t).Adj u v := by simpa using he
    cases u with
    | inl a =>
      cases a
      cases v with
      | inl b => exact False.elim ha
      | inr b =>
        rcases b with ⟨j,v⟩
        have hv : v=5 := ha
        subst v
        exact ⟨(j,7),by simp [edge,ends,node,hub,Sym2.eq_swap]⟩
    | inr a =>
      rcases a with ⟨i,u⟩
      cases v with
      | inl b =>
        cases b
        have hu : u=5 := ha
        subst u
        exact ⟨(i,7),rfl⟩
      | inr b =>
        rcases b with ⟨j,v⟩
        have hij : i=j := ha.1
        subst j
        have hl := ha.2
        fin_cases u <;> fin_cases v <;>
          simp [localAdj] at hl <;>
          solve | exact ⟨(i,0),by simp [edge,ends,node]⟩
                | exact ⟨(i,1),by simp [edge,ends,node]⟩
                | exact ⟨(i,2),by simp [edge,ends,node]⟩
                | exact ⟨(i,3),by simp [edge,ends,node]⟩
                | exact ⟨(i,4),by simp [edge,ends,node]⟩
                | exact ⟨(i,5),by simp [edge,ends,node]⟩
                | exact ⟨(i,6),by simp [edge,ends,node]⟩
theorem edgeFinset_eq (t : ℕ) : (graph t).edgeFinset = Finset.univ.image (@edge t) := by
  ext e
  constructor
  · intro h
    obtain ⟨ik,rfl⟩ := edge_surjective e h
    exact Finset.mem_image.mpr ⟨ik,Finset.mem_univ _,rfl⟩
  · intro h
    obtain ⟨ik,_,rfl⟩ := Finset.mem_image.mp h
    exact edge_is_edge ik
theorem edge_card (t : ℕ) : (graph t).edgeFinset.card = 8*t := by
  rw [edgeFinset_eq,Finset.card_image_of_injective _ (edge_injective t)]
  simp [Nat.mul_comm]
end
end EdgeIrregulator
