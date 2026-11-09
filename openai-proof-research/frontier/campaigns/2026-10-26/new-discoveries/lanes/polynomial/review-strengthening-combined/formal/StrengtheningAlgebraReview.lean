import Mathlib
namespace StrengtheningAlgebraReview

def H (A B C u v w : ℝ) := A*B*C-A*v*w-B*u*w-C*u*v-2*u*v*w

def D (u a b c y : ℝ) := u*(b+c-8*u-4*y)+b*(y+a)+c*(2*y+a+b)

lemma quadratic_difference (u v a b c y : ℝ) :
    H (v+y+a) (v+y+b) (v+c) u v (v+y) -
      H (u+y+a) (u+y+b) (u+c) u u (u+y) =
      (v-u)*(D u a b c y+(b+c-4*u)*(v-u)) := by unfold H D;ring

lemma derivative_sos (u a b c y : ℝ) (he : 2*(a+b+c)+y=6*u) :
    12*D u a b c y = -31*u^2-(3*(b+c)-8*u)^2-(3*y-u)^2-
      12*y*b-3*(b-c)^2-18*y*a := by
  have ha : a=3*u-y/2-b-c := by linarith
  rw [ha]
  unfold D
  ring

lemma case1 (u w A C : ℝ) (he : 4*A+2*C=9*u+3*w) :
    32*(2*u*w-C*(A-u)) = (4*C-5*u-3*w)^2+(w-u)*(25*u-9*w) := by
  have hA : A=(9*u+3*w-2*C)/4 := by linarith
  rw [hA]
  ring

lemma case2 (u w C d : ℝ) (he : 4*(w+d)+2*C=9*u+3*w) :
    2*(2*u*w-C*(w+d-u)) = (w-3*u)^2+d*(5*w-13*u)+4*d^2 := by
  have hC : C=(9*u-w-4*d)/2 := by linarith
  rw [hC]
  ring

lemma strict_perturbation (A B C u v w d : ℝ) :
    H (A+d) (B+d) (C+d) u v w-H A B C u v w =
      d*((A*B-u*v)+(A*C-u*w)+(B*C-v*w))+d^2*(A+B+C)+d^3 := by unfold H;ring

end StrengtheningAlgebraReview
