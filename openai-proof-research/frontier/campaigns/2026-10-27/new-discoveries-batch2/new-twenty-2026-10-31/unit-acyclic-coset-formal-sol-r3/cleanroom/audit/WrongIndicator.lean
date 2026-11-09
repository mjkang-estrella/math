import Sequence
open UnitCoset
example : multiplicity identity (0,0) = 0 := by
  rw [indicator identity identity_unit]
  decide
