/-! Focused audit of the literal Boolean penalty in Lin et al.,
DOI 10.23919/ICN.2026.0017, Eq. (22). This checks the named local
constraint only, not the full objective or any reported experiment.
See research/findings/H020-penalty-source-audit.md for source review. -/
namespace Research.AndPenaltyAudit

def bit (a : Bool) : Int := if a then 1 else 0

def penalty (a b c : Bool) : Int :=
  bit a * bit b - bit a * bit c - bit b * bit c + bit c

/-- The literal expression has no negative Boolean values. -/
theorem nonnegative : ∀ a b c : Bool, 0 ≤ penalty a b c := by
  decide +kernel

/-- Its zero set is not exactly the intended AND constraint. -/
theorem not_exact : ¬ (∀ a b c : Bool,
    penalty a b c = 0 ↔ c = (a && b)) := by
  decide +kernel

/-- Scaling cannot remove this false zero, even at a positive weight.
Together with nonnegativity, it is a false minimum of the local penalty. -/
theorem weighted_false_zero (weight : Int) :
    weight * penalty false true true = 0 ∧
    (true : Bool) ≠ (false && true) := by
  simp [penalty, bit]

end Research.AndPenaltyAudit
