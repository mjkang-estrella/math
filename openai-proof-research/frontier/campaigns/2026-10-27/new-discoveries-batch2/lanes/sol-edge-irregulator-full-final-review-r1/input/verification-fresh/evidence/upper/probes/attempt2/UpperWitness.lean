import Degrees
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator.Upper
open SimpleGraph
noncomputable section
attribute [local instance 10] Classical.propDecidable
def selected (k : Fin 3) : Fin 8 := ![0,2,6] k
theorem selected_injective : Function.Injective selected := by
  intro k l h
  fin_cases k <;> fin_cases l <;> simp_all [selected]
def index {t : ℕ} (ik : Fin t × Fin 3) : Fin t × Fin 8 := (ik.1, selected ik.2)
theorem index_injective (t : ℕ) : Function.Injective (@index t) := by
  rintro ⟨i,k⟩ ⟨j,l⟩ h
  have hi : i=j := congrArg Prod.fst h
  have hk : k=l := selected_injective (congrArg Prod.snd h)
  simp_all
def deletion (t : ℕ) : Finset (Sym2 (Vertex t)) :=
  Finset.univ.image (fun ik : Fin t × Fin 3 => edge (index ik))
theorem deletion_subset (t : ℕ) : deletion t ⊆ (graph t).edgeFinset := by
  intro e he
  obtain ⟨ik,_,rfl⟩ := Finset.mem_image.mp he
  exact edge_is_edge _
theorem deletion_card (t : ℕ) : (deletion t).card = 3*t := by
  rw [deletion, Finset.card_image_of_injective _ (show Function.Injective (fun ik => edge (index ik)) from (edge_injective t).comp (index_injective t))]
  simp [Nat.mul_comm]
theorem edge_mem_deletion {t : ℕ} (i : Fin t) (k : Fin 8) :
    edge (i,k) ∈ deletion t ↔ k=0 ∨ k=2 ∨ k=6 := by
  constructor
  · intro h
    obtain ⟨⟨j,l⟩,_,h⟩ := Finset.mem_image.mp h
    have hk : selected l = k := congrArg Prod.snd (edge_injective t h)
    fin_cases l <;> simp_all [selected]
  · intro h
    rcases h with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨(i,0),Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨(i,1),Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨(i,2),Finset.mem_univ _,rfl⟩
end
end EdgeIrregulator.Upper
