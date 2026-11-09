import Mathlib.Logic.Relation
example (x y : Nat × Nat) (h2 : ∃ hh : x.1 < y.1, True) : True := by
  obtain ⟨hlt, hw⟩ := h2
  trivial
