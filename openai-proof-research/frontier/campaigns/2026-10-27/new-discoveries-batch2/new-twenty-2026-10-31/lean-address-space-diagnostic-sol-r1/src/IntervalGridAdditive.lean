import IntervalFiniteGrid
import Mathlib.Algebra.Order.Monoid.Defs
namespace IntervalWidth
variable {α K : Type*} [LinearOrder α] [AddCommMonoid K] [PartialOrder K]
  [IsOrderedAddMonoid K]
/-- Deterministic finite-grid envelope, generic over ordered additive monoids.
This includes real CDFs once a kernel-certified real import is available. -/
theorem cdf_grid_envelope (h : Nat) (hh : 0 < h) (grid : Nat → α) (C F : α → K)
    (hC : Monotone C) (hF : Monotone F) (E delta : K)
    (err : ∀ q ≤ h, C (grid q) ≤ F (grid q)+E ∧ F (grid q) ≤ C (grid q)+E)
    (step : ∀ q < h, F (grid (q+1)) ≤ F (grid q)+delta)
    (x : α) (lo : grid 0 ≤ x) (hi : x ≤ grid h) :
    C x ≤ F x+(E+delta) ∧ F x ≤ C x+(E+delta) := by
  obtain ⟨q,hq,hlo,hhi⟩ := grid_bracket grid h hh x lo hi
  have e0 := err q (Nat.le_of_lt hq)
  have e1 := err (q+1) (Nat.succ_le_of_lt hq)
  have st := step q hq
  constructor
  · calc
      C x ≤ C (grid (q+1)) := hC hhi
      _ ≤ F (grid (q+1))+E := e1.1
      _ ≤ (F (grid q)+delta)+E := add_le_add st le_rfl
      _ ≤ (F x+delta)+E := add_le_add (add_le_add (hF hlo) le_rfl) le_rfl
      _ = F x+(E+delta) := by simp only [add_assoc, add_comm delta E]
  · calc
      F x ≤ F (grid (q+1)) := hF hhi
      _ ≤ F (grid q)+delta := st
      _ ≤ (C (grid q)+E)+delta := add_le_add e0.2 le_rfl
      _ ≤ (C x+E)+delta := add_le_add (add_le_add (hC hlo) le_rfl) le_rfl
      _ = C x+(E+delta) := by rw [add_assoc]
#print axioms cdf_grid_envelope
end IntervalWidth
