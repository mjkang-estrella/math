import PolynexusLiteral
example : 120*(psi 1 : ℤ) = (1+1:ℤ)^7-1^7+(1+1:ℤ)^3+1^3 := by
  rw [polynexus_one]
  norm_num
