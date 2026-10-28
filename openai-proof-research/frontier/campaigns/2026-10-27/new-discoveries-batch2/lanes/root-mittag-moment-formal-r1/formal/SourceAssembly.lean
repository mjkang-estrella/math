import DifferenceCriterion

set_option autoImplicit false

open Filter

namespace MittagModulus

noncomputable def squaredApprox (a : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  Complex.normSq (approxTransform a N ((Real.sqrt t : ℂ) * Complex.I))

theorem squaredApprox_tendsto {a t : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (ht : 0 ≤ t) :
    Tendsto (fun N => squaredApprox a N t) atTop (nhds (sourceExpression a t)) := by
  have h := Complex.continuous_normSq.continuousAt.tendsto.comp
    (approxTransform_tendsto ha ha2 ((Real.sqrt t : ℂ) * Complex.I))
  rw [← sourceExpression_eq_normSq ha ht] at h
  exact h

/-- Conditional integration interface only. The positive-kernel representation must
be proved for the actual squared approximants before the source is resolved. -/
theorem sourceClaim_of_positiveMixedApprox
    (hpos : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∀ N : ℕ,
      PositiveMixedDifferences (squaredApprox a N)) :
    SourceClaim370772 := by
  intro a ha ha2
  have hdiff : PositiveMixedDifferences (sourceExpression a) :=
    PositiveMixedDifferences.of_tendsto_positive (hpos a ha ha2)
      (fun t ht => squaredApprox_tendsto ha ha2 ht.le)
  exact hdiff.completelyMonotone (sourceExpression_contDiff ha)

end MittagModulus
