import BunState

namespace Bun

/-- For any strict prefix `j < u`, the state transition returns the empty pair. -/
theorem stf_before_source (n u : Nat) :
    ∀ (j : Nat) (w : Asg n j), j < u → stf n u j w = (∅, ∅) := by
  intro j
  induction j with
  | zero =>
    intro w h
    have hu : ¬ (u = 0) := by omega
    simp [stf, hu]
  | succ k ih =>
    intro w h
    simp [stf, h]

end Bun
