import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace JacobiShifted.Midpoint
open Polynomial
abbrev ZPoly := Polynomial ℤ
def q : ZPoly := 1 + X ^ 2
abbrev R := QuadraticAlgebra ZPoly q 0
def C : ZPoly →+* R := algebraMap ZPoly R
def x : R := ⟨X,0⟩
def w : R := ⟨0,1⟩
example : w^2 = 1+x^2 := by
 rw [pow_two, pow_two]
 apply QuadraticAlgebra.ext
 · rw [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul]
   simp [w,x,q, QuadraticAlgebra.re_one, pow_two]
 · rw [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul]
   simp [w,x, QuadraticAlgebra.im_one]
set_option pp.all true in
#check w ^ 2
set_option pp.all true in
#check w*w
end JacobiShifted.Midpoint
