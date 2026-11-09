import Chord6Final
open Chord
example (D : Diagram 0) (c : Sides 0) : boundary D c = 0 := by
  have h := empty_boundary D c
  omega
