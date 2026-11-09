import RealBridge
open Kirchhoff Matrix
example : ¬ Penrose LOne GIOne := by
  intro h
  have e := penrose_unique h validMPOne
  have c := congrFun (congrFun e 0) 0
  norm_num [GIOne, MPOne] at c
example : ¬ Penrose LOne (MPOne + Matrix.single 0 0 1) := by
  intro h
  have e := penrose_unique h validMPOne
  have c := congrFun (congrFun e 0) 0
  norm_num [MPOne, Matrix.single] at c
example : pairIndex MPOne ≠ 3196445304/78509585 := by
  rw [mp1]
  norm_num
