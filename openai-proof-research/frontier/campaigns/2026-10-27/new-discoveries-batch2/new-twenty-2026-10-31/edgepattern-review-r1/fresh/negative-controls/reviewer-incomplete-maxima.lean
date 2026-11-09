import EvalR3_0001
open EdgePattern EdgePattern.TreeModelsR3
example : MaskR3.best (graph ⟨0,0,0,1⟩) = {60,78} := by
  rw [best_0001]
  decide
