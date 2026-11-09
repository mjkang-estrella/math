import LowerWeighted
open WheelFormal
example (s : WheelSet 2) : (∑ v ∈ s, vertexWeight 2 v) ≤ 2*(2*(2:ℝ)^2+2+1) := by
  apply vertexWeight_independent_bound 2 (by norm_num) s
