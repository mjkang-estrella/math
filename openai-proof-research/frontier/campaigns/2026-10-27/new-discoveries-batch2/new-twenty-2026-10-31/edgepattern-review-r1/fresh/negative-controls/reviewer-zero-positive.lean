import Concrete
open EdgePattern
example : ∀ i : Fin 3, 0 < (![0,7/27,1/3] : Fin 3 → ℚ) i := by
  intro i
  fin_cases i <;> norm_num
