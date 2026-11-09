import GridExceptional
open Grid343536
example : Nonempty (EqPart (G 3 3) ≃o Subgroup (G 3 3 ≃g G 3 3)) := by
  exact exceptional_no_iso 3 (by decide) (by decide)
