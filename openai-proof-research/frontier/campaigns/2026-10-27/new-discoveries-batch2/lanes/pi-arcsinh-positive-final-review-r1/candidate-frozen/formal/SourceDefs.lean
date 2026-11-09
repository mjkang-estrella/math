import Mathlib

set_option autoImplicit false

noncomputable section
open Set

namespace ArcsinhPositive

/-- Literal integrand of the generalized inverse hyperbolic sine. -/
def sourceIntegrand (p t : ℝ) : ℝ := (1 + t ^ p) ^ (-(1 / p))

/-- Source equation (1.14), with a genuine interval integral. -/
def sourceArcsinh (p x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, sourceIntegrand p t

/-- The full parameter statement of Yin--Huang--Wang--Lin Conjecture 5.1. -/
def SourceConjecture : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 →
    StrictConcaveOn ℝ (Ioi (1 : ℝ)) (fun p ↦ sourceArcsinh p x)

def entropyExpression (u : ℝ) : ℝ := Real.log (1 + u) - u * Real.log u / (1 + u)

end ArcsinhPositive
