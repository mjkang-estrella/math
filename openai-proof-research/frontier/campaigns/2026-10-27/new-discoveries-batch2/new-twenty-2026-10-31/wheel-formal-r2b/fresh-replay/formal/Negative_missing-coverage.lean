import UpperIndexed
open WheelFormal
example (G : SimpleGraph (Fin 1)) (sets : Unit → {s : Finset (Fin 1) // Independent G s}) : FractionalColouring G := by
  apply indexedColouring G sets (fun _ => 0) (by intro i; norm_num)
