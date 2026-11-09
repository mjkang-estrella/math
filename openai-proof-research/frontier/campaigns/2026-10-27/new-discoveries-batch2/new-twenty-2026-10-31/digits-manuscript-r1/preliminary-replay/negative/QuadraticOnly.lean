import Digits
-- The exceptional progression (5,0,8,3) has quadratic-only gap -120.
example : (0 : ℤ) ≤ 4*5^2 + 4*3^2 - 4*0^2 - 4*8^2 := by
  norm_num
