import RotationCheck
open Schrijver
set_option maxRecDepth 20000
set_option exponentiation.threshold 100000
example : rotationBitsCheck 28 0 (maskAt28 0) (maskAt28 1) = true := by decide
