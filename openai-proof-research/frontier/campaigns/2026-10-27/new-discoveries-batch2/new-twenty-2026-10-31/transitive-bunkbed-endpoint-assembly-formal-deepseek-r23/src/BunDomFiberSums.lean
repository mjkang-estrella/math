import BunDomRows
namespace BunDom
open Classical Finset Bun
noncomputable local instance (j : Nat) : DecidableEq (Fin (j+1)) := Classical.decEq _
theorem rows_sum (j : Nat) (P Q : Fin (j+1) → Prop) (H : Bool → Bool → Bool → Nat) :
    (∑ f : Fresh j, H (hit P (fun i => f.1 i false)) (hit Q (fun i => f.1 i true)) f.2) =
    ∑ x : Bool, ∑ y : Bool, ∑ z : Bool, rowCount P x * rowCount Q y * H x y z := by
  let g : Fresh j → Bool × Bool × Bool := fun f =>
    (hit P (fun i => f.1 i false), hit Q (fun i => f.1 i true), f.2)
  rw [← Fintype.sum_fiberwise g]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  have he : Fintype.card {f : Fresh j // g f = (x,y,z)} = rowCount P x * rowCount Q y := by
    have e : {f : Fresh j // g f = (x,y,z)} ≃
        {f : Fresh j // hit P (fun i => f.1 i false) = x ∧ hit Q (fun i => f.1 i true) = y ∧ f.2 = z} :=
      Equiv.subtypeEquivRight (fun f => by simp only [g, Prod.mk.injEq])
    exact (Fintype.card_congr e).trans (rows_card j P Q x y z)
  calc
    _ = ∑ _f : {f : Fresh j // g f = (x,y,z)}, H x y z := by
      apply Finset.sum_congr rfl
      intro f _
      have hf := f.2
      change (hit P (fun i => f.1.1 i false), hit Q (fun i => f.1.1 i true), f.1.2) = (x,y,z) at hf
      exact congrArg (fun t : Bool × Bool × Bool => H t.1 t.2.1 t.2.2) hf
    _ = _ := by simp [he, Nat.mul_comm]
noncomputable def freshInd (j : Nat) (P Q : Fin (j+1) → Prop) (f : Fresh j) : Bool × Bool :=
  ind (hit P (fun i => f.1 i false)) (hit Q (fun i => f.1 i true)) f.2
noncomputable def incrementWeight (j : Nat) (P Q : Fin (j+1) → Prop) (d : Bool × Bool) : Nat :=
  ∑ x : Bool, ∑ y : Bool, ∑ z : Bool,
    rowCount P x * rowCount Q y * (if ind x y z = d then 1 else 0)
theorem increment_card (j : Nat) (P Q : Fin (j+1) → Prop) (d : Bool × Bool) :
    Fintype.card {f : Fresh j // freshInd j P Q f = d} = incrementWeight j P Q d := by
  rw [Fintype.card_subtype, Finset.card_filter]
  exact rows_sum j P Q (fun x y z => if ind x y z = d then 1 else 0)
theorem increment_four (j : Nat) (P Q : Fin (j+1) → Prop) :
    incrementWeight j P Q (false,false) = rowCount P false * rowCount Q false * 2 ∧
    incrementWeight j P Q (true,false) = rowCount P true * rowCount Q false ∧
    incrementWeight j P Q (false,true) = rowCount P false * rowCount Q true ∧
    incrementWeight j P Q (true,true) =
      rowCount P true * rowCount Q true * 2 +
      rowCount P true * rowCount Q false + rowCount P false * rowCount Q true := by
  simp [incrementWeight, ind, Nat.mul_two, Nat.add_comm]
end BunDom
