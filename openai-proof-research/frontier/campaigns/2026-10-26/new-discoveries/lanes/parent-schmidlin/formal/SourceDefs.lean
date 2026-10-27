import Mathlib

namespace Schmidlin

noncomputable def gammaError (z : ℝ) : ℝ :=
  Real.log (Real.Gamma z) - ((z-1/2)*Real.log z-z+Real.log (2*Real.pi)/2)

noncomputable def expandedError (x alpha : ℝ) : ℝ :=
  Real.log (Real.Gamma (x+1)) + alpha*Real.log (x+1) -
    (Real.log (2*Real.pi)/2 + (x+alpha+1/2)*Real.log (x+alpha+1/2) -
      (x+alpha+1/2))

noncomputable def interpolatedPi (x alpha : ℝ) : ℝ :=
  Real.Gamma (x+1) * (x+1)^alpha

noncomputable def burnsideStirling (y : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi) * Real.exp (-1/2) * (y+1/2)^(y+1/2) * Real.exp (-y)

noncomputable def sourceError (x alpha : ℝ) : ℝ :=
  Real.log (interpolatedPi x alpha / burnsideStirling (x+alpha))

def SourceConjecture372858 : Prop :=
  ∀ x alpha : ℝ, 0 ≤ x → 0 ≤ alpha → alpha ≤ 1 →
    sourceError x alpha ≤ 1/(12*(x+alpha)+18-12*Real.exp (1/48))

end Schmidlin
