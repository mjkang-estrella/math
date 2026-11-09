module
public import ParkingScalar
public section
open ParkingScalar
theorem positive_fixed : theta1 (1:ℚ) 1 = 1 ∧ theta2 (1:ℚ) 1 = 1 := by
  constructor
  · unfold theta1; ring
  · unfold theta2; ring
theorem positive_origin : theta1 (0:ℚ) 0 = 0 ∧ theta2 (0:ℚ) 0 = 0 := by
  constructor
  · unfold theta1; ring
  · unfold theta2; ring
theorem arithmetic_gap : 46 < (3*3+1)^2 := by decide
#print axioms positive_fixed
#print axioms positive_origin
#print axioms arithmetic_gap
