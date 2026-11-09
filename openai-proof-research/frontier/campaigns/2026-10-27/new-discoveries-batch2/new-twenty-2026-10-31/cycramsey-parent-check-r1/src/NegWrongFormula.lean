import CycMain
open CycRamsey
example : cycRamsey (startStar 3) (monPath 4) = 7 := by
  rw [cycRamsey_startStar_monPath 3 4 le_rfl le_rfl]
