import Mathlib

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Set Filter Topology

namespace GammaLevel

def logDefect (x s : ℝ) : ℝ :=
  Real.log (Real.Gamma (s - x)) + Real.log (Real.Gamma (s + x)) -
    2 * Real.log (Real.Gamma s)

def profile (u : ℝ) : ℝ := -Real.log (1 - u⁻¹ ^ 2)

def seriesTerm (x s : ℝ) (m : ℕ) : ℝ := profile ((s + m) / x)

def SourceLevel (c x y : ℝ) : Prop :=
  0 < y ∧ Real.Gamma y * Real.Gamma (y + 2 * x) /
    Real.Gamma (y + x) ^ 2 = c

def SourceConvexity : Prop :=
  ∀ c : ℝ, 1 < c → ∃ h : ℝ → ℝ,
    (∀ x : ℝ, 0 < x → SourceLevel c x (h x)) ∧
    StrictConvexOn ℝ (Ioi 0) h

end GammaLevel
