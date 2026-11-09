import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.Monotone.Basic
namespace IntervalWidth
variable {α : Type*} [LinearOrder α]
theorem grid_bracket (grid : Nat → α) (h : Nat) (hh : 0 < h)
    (x : α) (lo : grid 0 ≤ x) (hi : x ≤ grid h) :
    ∃ q < h, grid q ≤ x ∧ x ≤ grid (q+1) := by
  induction h with
  | zero => omega
  | succ h ih =>
    by_cases hz : h = 0
    · subst h
      exact ⟨0, by omega, lo, hi⟩
    · by_cases hx : x ≤ grid h
      · obtain ⟨q,hq,hlo,hhi⟩ := ih (by omega) hx
        exact ⟨q,by omega,hlo,hhi⟩
      · exact ⟨h, by omega, le_of_lt (lt_of_not_ge hx), hi⟩

/-- A finite grid controls every threshold between its endpoints. Count and model
functions are integer-scaled; delta is the adjacent model-count increment. -/
theorem finite_grid_envelope (h : Nat) (grid : Nat → α) (C F : α → Int)
    (hC : Monotone C) (hF : Monotone F) (E delta : Int)
    (err : ∀ q ≤ h, -E ≤ C (grid q)-F (grid q) ∧ C (grid q)-F (grid q) ≤ E)
    (step : ∀ q < h, F (grid (q+1))-F (grid q) ≤ delta)
    (x : α) (bracket : ∃ q < h, grid q ≤ x ∧ x ≤ grid (q+1)) :
    -(E+delta) ≤ C x-F x ∧ C x-F x ≤ E+delta := by
  obtain ⟨q,hq,lo,hi⟩ := bracket
  have c0 := hC lo
  have c1 := hC hi
  have f0 := hF lo
  have f1 := hF hi
  have e0 := err q (by omega)
  have e1 := err (q+1) (by omega)
  have hd := step q hq
  omega

/-- Finite maximum may be replaced by any bound holding on all grid points. -/
theorem finite_grid_uniform (h : Nat) (grid : Nat → α) (C F : α → Int)
    (hC : Monotone C) (hF : Monotone F) (E delta : Int)
    (err : ∀ q ≤ h, -E ≤ C (grid q)-F (grid q) ∧ C (grid q)-F (grid q) ≤ E)
    (step : ∀ q < h, F (grid (q+1))-F (grid q) ≤ delta)
    (hh : 0 < h) :
    ∀ x, grid 0 ≤ x → x ≤ grid h →
      -(E+delta) ≤ C x-F x ∧ C x-F x ≤ E+delta := by
  intro x hx hy
  exact finite_grid_envelope h grid C F hC hF E delta err step x (grid_bracket grid h hh x hx hy)
#print axioms grid_bracket
#print axioms finite_grid_envelope
#print axioms finite_grid_uniform
end IntervalWidth
