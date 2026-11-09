import Sequence
open UnitCoset
example : Acyclic identity := by
  exact no_acyclic_unit identity identity_unit
