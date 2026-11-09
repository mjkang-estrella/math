import Yip355956
set_option warningAsError true
namespace MathDB355956
variable {K : Type} [Field K]
theorem cube_0_copy (θ : K) (hθ : θ ^ 8 + θ ^ 7 + 2 * θ ^ 6 + 2 = 0) (h5 : (5 : K) = 0) :
    ((4) * θ + (3) * θ^2 + (3) * θ^3 + (2) * θ^4 + (3) * θ^5) ^ 3 = wit θ - 0 := by
  unfold wit
  linear_combination ((295) * 1 + (144) * θ + (28) * θ^2 + (154) * θ^3 + (107) * θ^4 + (36) * θ^5 + (27) * θ^6 + (27) * θ^7) * hθ + ((-118) * 1 + (-58) * θ + (-12) * θ^2 + (-49) * θ^3 + (-14) * θ^4 + (36) * θ^5 + (-61) * θ^6 + (-32) * θ^7) * h5

end MathDB355956
