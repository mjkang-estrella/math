import CrownVGraph
namespace CrownV
variable {n : ℕ}
open Classical
example {s : Finset (V n)} {x : V n} : ∀ z : V n, SameC (insert x s) x z → z = z ∨ True := by
  intro z h
  induction h with
  | @tail a b c h₁ h₂ ih => trace_state; sorry
  | refl => trivial
end CrownV
