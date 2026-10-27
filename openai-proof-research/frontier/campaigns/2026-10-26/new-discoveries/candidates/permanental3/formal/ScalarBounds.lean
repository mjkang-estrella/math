import Mathlib

namespace PermanentalThree

def normalizedNumerator (x y z w : ℝ) : ℝ := (1 + x) * (x * w + y * z)
def normalizedDenominator (x y z w : ℝ) : ℝ := x * (x * w + y * z + w + y + z + x)
def normalizedDet (x y z w : ℝ) : ℝ := x * w - y * z - w + y + z - x

theorem lower_certificate (x b c w : ℝ) :
    (x - 1) * (3 * normalizedNumerator x (x+b) (x+c) w -
      2 * normalizedDenominator x (x+b) (x+c) w) =
    2*x^2*(x-1)^2 + 2*x*(x+1)*(x-1)*(b+c) +
    (2*x^2+3*(x-1))*b*c + x*(x+1)*normalizedDet x (x+b) (x+c) w := by
  unfold normalizedNumerator normalizedDenominator normalizedDet
  ring

theorem upper_certificate (x b c w : ℝ) :
    (x - 1) * (9 * normalizedDenominator x (x+b) (x+c) w -
      8 * normalizedNumerator x (x+b) (x+c) w) =
    2*x^3*(x-1) + 20*x^2*(x-1) + 2*x*(x+1)*(x-1)*(b+c) +
    2*(x-2)^2*b*c + x*(x+1)*normalizedDet x (x+b) (x+c) w := by
  unfold normalizedNumerator normalizedDenominator normalizedDet
  ring

theorem normalized_strict_bounds {x y z w : ℝ}
    (hx : 1 < x) (hy : x < y) (hz : x < z)
    (hd : 0 < normalizedDet x y z w) :
    2 * normalizedDenominator x y z w < 3 * normalizedNumerator x y z w ∧
    8 * normalizedNumerator x y z w < 9 * normalizedDenominator x y z w := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hb : 0 < y - x := by linarith
  have hc : 0 < z - x := by linarith
  have hd' : 0 < normalizedDet x (x+(y-x)) (x+(z-x)) w := by
    simpa only [add_sub_cancel] using hd
  have hlo := lower_certificate x (y-x) (z-x) w
  have hhi := upper_certificate x (y-x) (z-x) w
  have hlpos : 0 < 2*x^2*(x-1)^2 + 2*x*(x+1)*(x-1)*((y-x)+(z-x)) +
      (2*x^2+3*(x-1))*(y-x)*(z-x) +
      x*(x+1)*normalizedDet x (x+(y-x)) (x+(z-x)) w := by positivity
  have hupos : 0 < 2*x^3*(x-1) + 20*x^2*(x-1) +
      2*x*(x+1)*(x-1)*((y-x)+(z-x)) + 2*(x-2)^2*(y-x)*(z-x) +
      x*(x+1)*normalizedDet x (x+(y-x)) (x+(z-x)) w := by positivity
  rw [← hlo] at hlpos
  rw [← hhi] at hupos
  have hl := (mul_pos_iff_of_pos_left hx1).mp hlpos
  have hu := (mul_pos_iff_of_pos_left hx1).mp hupos
  simp only [add_sub_cancel] at hl hu
  constructor <;> linarith

end PermanentalThree
