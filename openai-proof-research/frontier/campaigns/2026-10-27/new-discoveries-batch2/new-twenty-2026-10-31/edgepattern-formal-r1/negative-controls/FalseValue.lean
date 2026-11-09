import Concrete
open scoped BigOperators
example : (∑ i, EdgePattern.Concrete.alpha i * EdgePattern.Concrete.occupancy i) = 1 := by
  rw [EdgePattern.Concrete.separating_value]
  norm_num
