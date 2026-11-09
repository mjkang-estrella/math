import ConcreteR2
open EdgePattern EdgePattern.Concrete
example : expectation pattern 0 = 3/5 := by
  rw [expectation_values.1]
  norm_num
