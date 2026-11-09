import Sequence
open UnitCoset
example : sequence (constantSum 0) = [1] := by
  rw [constant_sequence]
  decide
