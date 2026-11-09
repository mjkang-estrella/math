import Final
open WheelFormal
example : fracChromatic (wheelSquare 1) = 5 := by
  have h := wheelSquare_fractional_eq 1 (by norm_num)
  norm_num at h ⊢
  linarith
