import Mathlib
noncomputable section
open Set Real
namespace SimonThreshold
/-- Literal elementary criterion in Simon's Section 3. -/
def SourceCriterion (γ α β : ℝ) : Prop :=
  ∀ z ∈ Ioo (0 : ℝ) 1, z + γ * (z ^ (β - α) - z ^ β) ≤ 1
/-- Literal source infimum over positive admissible beta. -/
def sourceThreshold (γ α : ℝ) : ℝ :=
  sInf {β : ℝ | 0 < β ∧ SourceCriterion γ α β}
def kernel (t : ℝ) : ℝ := -log (1 - exp (-t))
def envelope (γ α s : ℝ) : ℝ :=
  α + α / s * (log γ - kernel s + kernel (s / α))
end SimonThreshold
