import Literal
namespace Literal

theorem equivalent_trans {g h k : Graph} (a : Equivalent g h) (b : Equivalent h k) :
    Equivalent g k := by
  induction a with
  | refl => exact b
  | step move _ ih => exact Equivalent.step move (ih b)

theorem equivalent_symm {g h : Graph} (path : Equivalent g h) : Equivalent h g := by
  induction path with
  | refl => exact Equivalent.refl _
  | @step g h k move rest ih =>
    have back : YYDelta h g ∨ DeltaYY h g := by
      cases move with
      | inl down => exact Or.inr down
      | inr up => exact Or.inl up
    exact equivalent_trans ih (Equivalent.step back (Equivalent.refl _))

theorem pure_equivalent {g h : Graph} (path : Pure g h) : Equivalent g h := by
  induction path with
  | refl => exact Equivalent.refl _
  | step down _ ih => exact Equivalent.step (Or.inl down) ih
end Literal
