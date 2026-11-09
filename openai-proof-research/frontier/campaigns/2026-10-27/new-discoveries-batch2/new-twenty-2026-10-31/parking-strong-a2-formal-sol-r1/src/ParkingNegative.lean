module
public import ParkingScalar
public section
open ParkingScalar
-- Intentional mutation: replace the denominator 4 in the directional factor by 5.
example (x y : ℚ) : y*theta1 x y-x*theta2 x y=x*y*(x^3-y^3)^3/5 := by
  unfold theta1 theta2
  ring
