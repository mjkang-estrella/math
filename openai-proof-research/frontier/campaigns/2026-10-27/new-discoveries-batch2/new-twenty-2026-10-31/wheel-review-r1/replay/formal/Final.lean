import UpperAttaining
set_option autoImplicit false
namespace WheelFormal
/-- Conjecture 7.3, uniformly for every t >= 1, with no residual hypotheses. -/
theorem wheelSquare_fractional_eq (t : ℕ) (ht : 1 ≤ t) :
    fracChromatic (wheelSquare t) =
      (6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(t:ℝ)^2+(t:ℝ)+1) := by
  apply le_antisymm
  · have h := fracChromatic_le_total (wheelSquare t) (attainingColouring t)
    rwa [attainingColouring_total] at h
  · exact wheelSquare_fractional_lower t ht

/-- A proof of the exact inherited target proposition. -/
theorem target_proved : Target := wheelSquare_fractional_eq
end WheelFormal
#print axioms WheelFormal.target_proved
#print axioms WheelFormal.wheelSquare_fractional_eq
