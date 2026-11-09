import CMDRRTranspose
import Mathlib.GroupTheory.Perm.Cycle.Type
open scoped Classical BigOperators
open Equiv.Perm
namespace CMDRR.Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)

theorem spouse_row_sign (m : Fin 5) (hm : m.val < 3) :
    sign (h.rowPerm m) = -1 := by
  classical
  obtain ⟨x,c,h3,_,_,_,_,_,_,_,cover⟩ := h.spouse_row_four m hm
  have hcyc : (h.rowPerm m).IsCycle := by
    refine ⟨x,h.rowPerm_no_fixed m x,?_⟩
    intro y _
    rcases cover y with rfl | rfl | rfl | rfl
    · exact SameCycle.rfl
    · exact SameCycle.rfl.apply_right
    · exact SameCycle.rfl.apply_right.apply_right
    · rw [← h3]
      exact SameCycle.rfl.apply_right.apply_right.apply_right
  have hs : (h.rowPerm m).support = Finset.univ := by
    ext w
    simp only [mem_support,Finset.mem_univ,iff_true]
    exact h.rowPerm_no_fixed m w
  rw [hcyc.sign,hs,Finset.card_univ,canonical_row_card m hm]
  decide

theorem single_row_sign (m : Fin 5) (hm : 3 ≤ m.val) :
    sign (h.rowPerm m) = 1 := by
  classical
  let x : Row (s := canonical) m := ⟨0,fun hs => by have := hs.2; omega⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,cover⟩ := h.single_row_five m hm x
  have hcyc : (h.rowPerm m).IsCycle := by
    refine ⟨x,h.rowPerm_no_fixed m x,?_⟩
    intro y _
    rcases cover y with rfl | rfl | rfl | rfl | rfl
    · exact SameCycle.rfl
    · exact SameCycle.rfl.apply_right
    · exact SameCycle.rfl.apply_right.apply_right
    · exact SameCycle.rfl.apply_right.apply_right.apply_right
    · exact SameCycle.rfl.apply_right.apply_right.apply_right.apply_right
  have hs : (h.rowPerm m).support = Finset.univ := by
    ext w
    simp only [mem_support,Finset.mem_univ,iff_true]
    exact h.rowPerm_no_fixed m w
  rw [hcyc.sign,hs,Finset.card_univ,canonical_single_row_card m hm]
  decide

theorem row_sign (m : Fin 5) :
    sign (h.rowPerm m) = if m.val < 3 then -1 else 1 := by
  classical
  split_ifs with hm
  · exact h.spouse_row_sign m hm
  · exact h.single_row_sign m (by omega)

noncomputable def extendedRow (m : Fin 5) : Equiv.Perm (Fin 5) :=
  Equiv.Perm.ofSubtype (h.rowPerm m)
noncomputable def fullU : Equiv.Perm (Fin 5 × Fin 5) :=
  Equiv.prodCongrRight h.extendedRow

theorem extended_row_sign (m : Fin 5) :
    sign (h.extendedRow m) = if m.val < 3 then -1 else 1 :=
  (sign_ofSubtype (h.rowPerm m)).trans (h.row_sign m)

theorem full_U_sign : sign h.fullU = -1 := by
  classical
  change sign (Equiv.prodCongrRight h.extendedRow) = _
  rw [sign_prodCongrRight]
  simp only [h.extended_row_sign]
  decide
end CMDRR.Source
