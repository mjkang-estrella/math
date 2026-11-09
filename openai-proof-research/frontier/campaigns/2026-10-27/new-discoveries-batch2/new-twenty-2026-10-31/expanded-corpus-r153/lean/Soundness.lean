import Delta153
namespace Delta153
inductive PureReach : Graph → Graph → Prop
| refl (g : Graph) : PureReach g g
| step {g h : Graph} (x : Nat) (hx : x ∈ verts g) (hw : wye g x = true) :
    PureReach (reduce g x) h → PureReach g h

theorem lower_sound (f b : Nat) (g : Graph) (hc : pureLower f b g = true) :
    ∀ h, PureReach g h → b ≤ h.length := by
  induction f generalizing g with
  | zero =>
    simp only [pureLower, Bool.and_eq_true, decide_eq_true_eq] at hc
    intro h hr
    cases hr with
    | refl => exact hc.1
    | step x hx hw rest =>
      have hh := List.all_eq_true.mp hc.2 x hx
      simp [hw] at hh
  | succ f ih =>
    simp only [pureLower, Bool.and_eq_true, decide_eq_true_eq] at hc
    intro h hr
    cases hr with
    | refl => exact hc.1
    | step x hx hw rest =>
      have hh := List.all_eq_true.mp hc.2 x hx
      simp only [hw, Bool.not_true, Bool.false_or] at hh
      exact ih _ hh h rest

#print axioms lower_sound
end Delta153
