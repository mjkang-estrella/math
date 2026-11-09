import CMDRRRowSigns
open scoped Classical BigOperators
open Equiv.Perm
namespace CMDRR.Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)

theorem full_U_cell (x : Cell canonical) : (h.U x).1 = h.fullU x.1 := by
  change (h.U x).1 = (x.1.1, ofSubtype (h.rowPerm x.1.1) x.1.2)
  rw [ofSubtype_apply_of_mem (p := fun w : Fin 5 => ¬ canonical.spouse x.1.1 w)
    (a := x.1.2) (h.rowPerm x.1.1) x.2]
  exact congrArg Subtype.val (h.rowCell_perm x.1.1 ⟨x.1.2,x.2⟩).symm

theorem full_U_spouse (x : Fin 5 × Fin 5) (hx : canonical.spouse x.1 x.2) :
    h.fullU x = x := by
  change (x.1,ofSubtype (h.rowPerm x.1) x.2) = x
  exact congrArg (fun w => (x.1,w))
    (ofSubtype_apply_of_not_mem (p := fun w : Fin 5 => ¬ canonical.spouse x.1 w)
      (h.rowPerm x.1) (fun hn => hn hx))

theorem U_sign : sign h.U = -1 := by
  classical
  have he : sign h.U = sign h.fullU := by
    apply sign_bij (fun x _ => x.1)
    · intro x _ _
      exact h.full_U_cell x
    · intro a b _ _ he
      exact Subtype.ext he
    · intro y hy
      have hn : ¬ canonical.spouse y.1 y.2 := fun hs => hy (h.full_U_spouse y hs)
      refine ⟨⟨y,hn⟩,?_,rfl⟩
      intro he
      exact h.U_second_ne ⟨y,hn⟩ (congrArg (fun c : Cell canonical => c.1.2) he)
  exact he.trans h.full_U_sign

theorem C_sign : sign h.C = -1 := by
  classical
  have he : sign h.C = sign h.canonical_swap_source.U :=
    sign_eq_sign_of_equiv h.C h.canonical_swap_source.U canonicalTranspose
      (fun x => (h.swapped_U_is_C x).symm)
  exact he.trans h.canonical_swap_source.U_sign
end CMDRR.Source

namespace CMDRR
theorem canonical_spouse_count :
    count (fun p : Fin 5 × Fin 5 => canonical.spouse p.1 p.2) = 3 := by
  classical
  let e : {p : Fin 5 × Fin 5 // canonical.spouse p.1 p.2} ≃ Fin 3 :=
    { toFun := fun p => ⟨p.1.1.val,p.2.2⟩
      invFun := fun i => ⟨(⟨i.val,by omega⟩,⟨i.val,by omega⟩),⟨rfl,i.isLt⟩⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact p.2.1
      right_inv := fun i => rfl }
  rw [count_eq_card]
  exact Fintype.card_congr e

namespace Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)
theorem T_sign : sign h.T = -1 := by
  classical
  have hp : h.T ^ 2 = 1 := by
    ext x
    change h.T (h.T x) = x
    exact h.T_involutive x
  have hn : IsEmpty (Function.fixedPoints h.T) :=
    ⟨fun x => h.T_fixedPointFree x.1 x.2⟩
  have hc : Fintype.card (Cell canonical) = 22 :=
    cells_card canonical (by decide) (by decide) canonical_spouse_count
  have hz : Fintype.card (Function.fixedPoints h.T) = 0 := by
    exact Fintype.card_eq_zero
  rw [sign_of_pow_two_eq_one hp,hc,hz]
  decide

include h in
theorem canonical_sign_contradiction : False := by
  classical
  have he : h.T.trans h.C = h.U := by
    ext x
    exact h.C_T x
  have hs := congrArg sign he
  rw [sign_trans,h.C_sign,h.T_sign,h.U_sign] at hs
  simp at hs
end Source
end CMDRR
