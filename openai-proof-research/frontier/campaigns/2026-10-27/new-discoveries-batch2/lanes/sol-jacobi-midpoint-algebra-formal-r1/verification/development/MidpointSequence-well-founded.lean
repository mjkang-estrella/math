import MidpointAlgebra
import Riccati
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
set_option warningAsError true

noncomputable section
namespace JacobiShifted.Midpoint
open JacobiShifted.BinaryFiltration

abbrev Param := MvPolynomial (Fin 2) R
def P : Param := initial (w^2) (w*x)

/-- A finite well-founded construction, including both zero endpoints. -/
def h : ℕ → Param
  | 0 => 0
  | 1 => P
  | n+2 => -coefficientOperator delta (h (n+1)) -
      ∑ i : Fin (n+2), h i.val * h (n+1-i.val)
termination_by n => n

@[simp] theorem h_zero : h 0 = 0 := by rw [h]
@[simp] theorem h_one : h 1 = P := by rw [h]

theorem h_recurrence (n : ℕ) (hn : 1 ≤ n) :
    h (n+1) = -coefficientOperator delta (h n) -
      ∑ i ∈ Finset.range (n+1), h i*h (n-i) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [show k+1+1 = k+2 by omega, h]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => h i*h (k+1-i)) (k+2)

theorem h_weighted (n : ℕ) : Weighted (h n) :=
  riccati_initial_weighted delta (w^2) (w*x) h h_zero h_one h_recurrence n

theorem h_odd_coefficient_divisible (n i j d : ℕ) (hj : Odd j) (hd : d=i+j) :
    (2 : R)^sigma (d-1) ∣ (h n).coeff (bidegree i j) :=
  riccati_degree_odd_coefficient delta (w^2) (w*x) h h_zero h_one h_recurrence
    n i j d hj hd

end JacobiShifted.Midpoint
