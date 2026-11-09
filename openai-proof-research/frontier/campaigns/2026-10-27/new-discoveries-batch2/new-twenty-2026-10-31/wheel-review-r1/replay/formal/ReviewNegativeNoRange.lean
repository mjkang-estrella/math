import Final
open WheelFormal
example (t : ℕ) : fracChromatic (wheelSquare t) = (6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(t:ℝ)^2+t+1) := by
  exact target_proved t
