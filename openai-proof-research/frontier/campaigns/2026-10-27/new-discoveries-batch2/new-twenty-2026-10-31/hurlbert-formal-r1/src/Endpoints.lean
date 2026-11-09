import Hurlbert

namespace MathDB356266

/-- Every cyclic Euler ordering, at every positive permutation size, lifts
    to a cyclic word over some finite ordered alphabet. -/
def Conjecture : Prop :=
  ∀ (n N : Nat) (t : Fin (N+1) → Fin (n+1) → Fin (n+1)),
    EulerOrdering t → ∃ (K : Nat) (w : Fin (N+1) → Fin K), Realizes t w

/-- The same ordering assertion allowing an arbitrary linearly ordered type. -/
def ConjectureLinear : Prop :=
  ∀ (n N : Nat) (t : Fin (N+1) → Fin (n+1) → Fin (n+1)),
    EulerOrdering t → ∃ (A : Type) (_ : LinearOrder A) (w : Fin (N+1) → A),
      Realizes t w

theorem conjecture_false : ¬ Conjecture := by
  intro h
  obtain ⟨K, w, hw⟩ := h 3 23 tour tour_euler
  exact tour_not_realizable w hw

theorem conjectureLinear_false : ¬ ConjectureLinear := by
  intro h
  obtain ⟨A, inst, w, hw⟩ := h 3 23 tour tour_euler
  let := inst
  exact tour_not_realizable w hw

end MathDB356266
