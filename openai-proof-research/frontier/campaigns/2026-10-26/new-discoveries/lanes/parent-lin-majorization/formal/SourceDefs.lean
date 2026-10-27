import Mathlib

open scoped Matrix.Norms.Operator ComplexOrder MatrixOrder
open Matrix
namespace LinMajorization

abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

noncomputable def A : M3 :=
  !![3/10, -111/280, -23/129;
     -111/280, 3/5, 2227/9030;
     -23/129, 2227/9030, 9/10]
noncomputable def B : M3 :=
  !![1742720/83779, 1127560/83779, 0;
     1127560/83779, 826784/83779, 0;
     0, 0, 0]
noncomputable def Q : M3 :=
  !![381/421, 88/421, 156/421;
     -72/421, 411/421, -56/421;
     -164/421, 24/421, 387/421]
noncomputable def D : M3 := diagonal ![1,3/5,0]
noncomputable def L : M3 := A^2 + Q * D^3 * star Q
noncomputable def R : M3 := A^2 + D^3
noncomputable def tau : ℝ := 197/500
noncomputable def lower (l m n : ℂ) : M3 := !![1,0,0;l,1,0;m,n,1]

noncomputable def sourceLeft {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (p : ℝ) :=
  A^2 + CFC.rpow (CFC.abs (B*A)) p
noncomputable def sourceRight {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (p : ℝ) :=
  A^2 + CFC.rpow (CFC.abs (A*B)) p

end LinMajorization
