import Chord6Final
open Chord Chord.Round6 Equiv
example : cycles 2 (Chord.Model2.rawPerm ((1 : Perm (Fin 2)) * swap 0 1)) = 3 := by decide
