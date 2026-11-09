import Graph
open Kirchhoff
example : Penrose LOne (MPOne + Matrix.single 0 0 1) := by unfold Penrose; decide +kernel
