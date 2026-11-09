import BunDomPins
import BunDomZero
import BunDomRecursion
namespace BunDom
open Classical Bun
variable {α : Type} [Fintype α]
noncomputable def hit (P : α → Prop) (f : α → Bool) : Bool :=
  decide (∃ a, P a ∧ f a = true)
noncomputable def rowCount (P : α → Prop) (x : Bool) : Nat :=
  if x then 2 ^ Fintype.card α - 2 ^ (Fintype.card α - Fintype.card {a // P a})
  else 2 ^ (Fintype.card α - Fintype.card {a // P a})
theorem hit_false (P : α → Prop) (f : α → Bool) :
    hit P f = false ↔ ∀ a, P a → f a = false := by
  simp only [hit, decide_eq_false_iff_not, not_exists, not_and]
  constructor
  · intro h a ha; simpa using h a ha
  · intro h a ha; simp [h a ha]
theorem hit_card_eq (P : α → Prop) (x : Bool) :
    Fintype.card {f : α → Bool // hit P f = x} = rowCount P x := by
  cases x
  · exact (Fintype.card_congr (Equiv.subtypeEquivRight (hit_false P))).trans (pin_card P)
  · exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun f => by simp [hit]))).trans (hit_card P)
noncomputable local instance (j : Nat) : DecidableEq (Fin (j+1)) := Classical.decEq _
noncomputable def rowsEquiv (j : Nat) (P Q : Fin (j+1) → Prop) (x y z : Bool) :
    {f : Fresh j // hit P (fun i => f.1 i false) = x ∧
      hit Q (fun i => f.1 i true) = y ∧ f.2 = z} ≃
    ({r : Fin (j+1) → Bool // hit P r = x} ×
      {r : Fin (j+1) → Bool // hit Q r = y}) where
  toFun f := (⟨_, f.2.1⟩, ⟨_, f.2.2.1⟩)
  invFun r := ⟨(fun i l => if l then r.2.1 i else r.1.1 i, z), by simp [r.1.2, r.2.2]⟩
  left_inv f := by
    apply Subtype.ext
    apply Prod.ext
    · funext i l; cases l <;> rfl
    · exact f.2.2.2.symm
  right_inv r := by apply Prod.ext <;> apply Subtype.ext <;> rfl
 theorem rows_card (j : Nat) (P Q : Fin (j+1) → Prop) (x y z : Bool) :
    Fintype.card {f : Fresh j // hit P (fun i => f.1 i false) = x ∧
      hit Q (fun i => f.1 i true) = y ∧ f.2 = z} = rowCount P x * rowCount Q y := by
  rw [Fintype.card_congr (rowsEquiv j P Q x y z), Fintype.card_prod]
  exact congrArg₂ (fun a b : Nat => a*b) (hit_card_eq P x) (hit_card_eq Q y)
end BunDom
