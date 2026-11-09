import NutInterface
import CheckedGraphIso
namespace Nut8
def orderedTreeCheck (code : Nat) (order parents : List Nat) : Bool :=
  decide (order.Perm (List.range 8)) && decide (parents.length = 8) &&
    (List.range 8).all (fun i => if i = 0 then true else
      decide (parents[i]?.getD 8 < i) &&
      graphBit 8 code (order[parents[i]?.getD 8]?.getD 8) (order[i]?.getD 8))
end Nut8
namespace Nut8

theorem orderedTreeCheck_sound (code : Nat) (order parents : List Nat)
    (h : orderedTreeCheck code order parents = true) :
    ∃ e : Equiv.Perm (Fin 8), ∃ p : Fin 8 → Fin 8,
      ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧
        graphBit 8 code (e (p i)).val (e i).val = true := by
  have hh : order.Perm (List.range 8) ∧ parents.length = 8 ∧
      ∀ i ∈ List.range 8, (if i = 0 then true else
        decide (parents[i]?.getD 8 < i) &&
        graphBit 8 code (order[parents[i]?.getD 8]?.getD 8) (order[i]?.getD 8)) = true := by
    simpa only [orderedTreeCheck, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, and_assoc] using h
  have hi : ∀ i : Fin 8, i ≠ 0 → parents[i.val]?.getD 8 < i.val := by
    intro i hn
    have hn' : i.val ≠ 0 := fun he => hn (Fin.ext he)
    have hv := hh.2.2 i.val (List.mem_range.mpr i.isLt)
    simp only [hn', ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1
  let p : Fin 8 → Fin 8 := fun i => if hn : i = 0 then 0
    else ⟨parents[i.val]?.getD 8, lt_trans (hi i hn) i.isLt⟩
  refine ⟨checkedEquiv order hh.1, p, ?_⟩
  intro i hn
  have hp : (p i).val = parents[i.val]?.getD 8 := by simp [p, hn]
  refine ⟨by simpa only [hp] using hi i hn, ?_⟩
  rw [checkedVertex_lookup, checkedVertex_lookup, hp]
  have hn' : i.val ≠ 0 := fun he => hn (Fin.ext he)
  have hv := hh.2.2 i.val (List.mem_range.mpr i.isLt)
  simp only [hn', ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hv
  exact hv.2
end Nut8
