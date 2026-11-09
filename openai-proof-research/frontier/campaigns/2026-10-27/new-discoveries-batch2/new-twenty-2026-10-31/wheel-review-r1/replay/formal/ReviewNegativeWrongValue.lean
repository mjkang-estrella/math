import Final
open WheelFormal
example : fracChromatic (wheelSquare 1) = 3 := by
  have h := target_proved 1 (by norm_num)
  norm_num at h ⊢
  linarith
