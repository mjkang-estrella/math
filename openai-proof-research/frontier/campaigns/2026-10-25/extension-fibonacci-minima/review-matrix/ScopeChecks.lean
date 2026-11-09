import WeakMajorization
import CoefficientMinor
open Matrix Polynomial

example : Antitone WeakMajorizationCounterexample.H_fifth_hermitian.eigenvalues₀ :=
  WeakMajorizationCounterexample.H_fifth_hermitian.eigenvalues₀_antitone

example : Antitone WeakMajorizationCounterexample.R_fifth_hermitian.eigenvalues₀ :=
  WeakMajorizationCounterexample.R_fifth_hermitian.eigenvalues₀_antitone

example (x y z : ℝ) (i j : Fin 3) :
    ((((CoefficientMinorCounterexample.pencil i j).eval (C (C y))).eval (C z)).eval x) =
      (if i=j then 1 else 0) + x*CoefficientMinorCounterexample.D1 i j +
        y*CoefficientMinorCounterexample.D2 i j + z*CoefficientMinorCounterexample.D3 i j := by
  by_cases h : i=j <;> simp [CoefficientMinorCounterexample.pencil, h] <;> ring
