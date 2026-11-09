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

/-- Finite coefficient history, built solely by primitive natural-number recursion.
The new slot is the Riccati convolution of the already constructed finite prefix. -/
def history : (n : ℕ) → Fin (n+1) → Param :=
  Nat.rec (motive := fun n => Fin (n+1) → Param)
    (fun _ => 0)
    (fun n prev i =>
      if hi : i.val < n+1 then prev ⟨i.val,hi⟩
      else if n=0 then P
      else -coefficientOperator delta (prev ⟨n, by omega⟩) -
        ∑ k : Fin (n+1), prev k * prev ⟨n-k.val, by omega⟩)

/-- The diagonal of the concrete finite-history construction. -/
def h (n : ℕ) : Param := history n (Fin.last n)

@[simp] theorem h_zero : h 0 = 0 := rfl
@[simp] theorem h_one : h 1 = P := by simp [h, history]

theorem history_agrees (n : ℕ) (i : Fin (n+1)) : history n i = h i.val := by
  induction n with
  | zero =>
    have he : i=Fin.last 0 := Fin.ext (by simp only [Fin.val_last]; omega)
    subst i
    rfl
  | succ n ih =>
    by_cases hi : i.val < n+1
    · change (if hlt : i.val<n+1 then history n ⟨i.val,hlt⟩ else _) = h i.val
      rw [dite_eq_left hi]
      exact ih ⟨i.val,hi⟩
    · have he : i=Fin.last (n+1) := Fin.ext (by simp only [Fin.val_last]; omega)
      subst i
      rfl

theorem h_recurrence (n : ℕ) (hn : 1 ≤ n) :
    h (n+1) = -coefficientOperator delta (h n) -
      ∑ i ∈ Finset.range (n+1), h i*h (n-i) := by
  have hn0 : n ≠ 0 := by omega
  change (if hi : n+1<n+1 then history n ⟨n+1,hi⟩ else
    if n=0 then P else -coefficientOperator delta (history n ⟨n, by omega⟩) -
      ∑ k : Fin (n+1), history n k * history n ⟨n-k.val, by omega⟩) = _
  simp only [lt_self_iff_false, dite_false, hn0, ite_false]
  simp_rw [history_agrees]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => h i*h (n-i)) (n+1)

theorem h_weighted (n : ℕ) : Weighted (h n) :=
  riccati_initial_weighted delta (w^2) (w*x) h h_zero h_one h_recurrence n

theorem h_odd_coefficient_divisible (n i j d : ℕ) (hj : Odd j) (hd : d=i+j) :
    (2 : R)^sigma (d-1) ∣ (h n).coeff (bidegree i j) :=
  riccati_degree_odd_coefficient delta (w^2) (w*x) h h_zero h_one h_recurrence
    n i j d hj hd

end JacobiShifted.Midpoint
