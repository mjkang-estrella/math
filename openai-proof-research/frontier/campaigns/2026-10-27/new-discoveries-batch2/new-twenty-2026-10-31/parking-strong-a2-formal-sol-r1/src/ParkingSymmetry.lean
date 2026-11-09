module
public import ParkingScalar
public section
namespace ParkingSymmetry
open ParkingScalar
variable {K : Type*} [Field K] [CharZero K]

theorem swap (x y : K) : theta1 y x = theta2 x y := by
  unfold theta1 theta2
  ring

theorem rotation1 (z x y : K) (hz : z^3 = 1) :
    theta1 (z*x) (z^2*y) = z*theta1 x y := by
  calc _ = ((z^3)^3*z*x^10+3*(z^3)^5*z*x^4*y^6)/4 := by unfold theta1; ring
       _ = z*theta1 x y := by rw [hz]; unfold theta1; ring

theorem rotation2 (z x y : K) (hz : z^3 = 1) :
    theta2 (z*x) (z^2*y) = z^2*theta2 x y := by
  calc _ = ((z^3)^6*z^2*y^10+3*(z^3)^4*z^2*x^6*y^4)/4 := by unfold theta2; ring
       _ = z^2*theta2 x y := by rw [hz]; unfold theta2; ring

theorem linear_independence (a b : K)
    (h : ∀ x y, a*theta1 x y+b*theta2 x y = 0) : a = 0 ∧ b = 0 := by
  constructor
  · calc a = 4*(a*theta1 1 0+b*theta2 1 0) := by unfold theta1 theta2; ring
         _ = 0 := by rw [h]; ring
  · calc b = 4*(a*theta1 0 1+b*theta2 0 1) := by unfold theta1 theta2; ring
         _ = 0 := by rw [h]; ring

#print axioms swap
#print axioms rotation1
#print axioms rotation2
#print axioms linear_independence
end ParkingSymmetry
