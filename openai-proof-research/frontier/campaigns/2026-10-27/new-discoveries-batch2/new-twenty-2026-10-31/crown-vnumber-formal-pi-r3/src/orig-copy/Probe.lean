import CrownVGraph
namespace Probe
-- 2-ary-ish motive: x appears in goal via f
example {α} {r : α → α → Prop} {x y : α} (h : Relation.ReflTransGen r x y) (f g : α → α) :
    True := by
  induction h with
  | refl => trivial
  | tail h₁ h₂ h₃ =>
    trace_state
    trivial
end Probe
