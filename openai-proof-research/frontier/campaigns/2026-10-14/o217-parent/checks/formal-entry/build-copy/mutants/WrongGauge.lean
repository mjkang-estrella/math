import Controls
open O217 O217Controls
example : edgeSpin (flipSpin 0 plus) edge01 = edgeSpin plus edge01 := by
  norm_num [edgeSpin, flipSpin, spinSign, plus, edge01]
