import MiddleFinal
open R139.MiddleOCD
example : (middle G8).Adj (Sum.inl 0) (Sum.inl 1) := by
  change False
  decide
