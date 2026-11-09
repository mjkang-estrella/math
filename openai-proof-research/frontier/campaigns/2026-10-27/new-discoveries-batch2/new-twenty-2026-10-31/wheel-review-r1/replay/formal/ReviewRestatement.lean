import Final
open scoped BigOperators
open WheelFormal
set_option autoImplicit false
-- Source-language restatement expands every potentially weakened wrapper.
theorem reviewer_source_statement (t : ℕ) (ht : 1 ≤ t) :
    sInf (Set.range (fun c : FractionalColouring
      ((wheel (2*t+1)).boxProd (wheel (2*t+1))) =>
        ∑ s, c.weight s)) =
    (6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(t:ℝ)^2+(t:ℝ)+1) := by
  exact target_proved t ht
#print axioms reviewer_source_statement
