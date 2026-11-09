import CycMain
open CycRamsey
example : cycRamsey (startStar 4) (monPath 3) = 1 + (4 - 1) * (3 - 2) :=
  cycRamsey_startStar_monPath 4 3 le_rfl le_rfl
