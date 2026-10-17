import IndependentControls
open O217 IndependentO217
-- The incident-edge condition cannot be discarded from the sign rule.
example : edgeSpin (flipSpin 0 (fun _ : Fin 3 => false)) e12 = -1 := by
  norm_num [edgeSpin,flipSpin,spinSign,e12]
