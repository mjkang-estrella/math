import Mathlib.Data.Finset.Card
example (m : Nat) (R : Finset Nat) (p : {x // x ∈ Finset.range m} → Bool) : Bool :=
  decide (((Finset.range m).attach.filter fun t => R.contains t.1 && p t).Nonempty)
example (j : Nat) (h : j ≤ j + 1) : True := trivial
#check @Nat.le_succ
#check @Finset.decidableNonempty
