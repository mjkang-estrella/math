import EvalR3_0000
open EdgePattern.TreeModelsR3
example : 2 ≤ occupancy ⟨0,0,0,0⟩ 0 := by
  norm_num [occupancy,totals_0000.1,count_0000]
