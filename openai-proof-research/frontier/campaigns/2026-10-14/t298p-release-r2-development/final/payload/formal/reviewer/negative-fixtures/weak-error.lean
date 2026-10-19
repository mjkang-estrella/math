import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace T298P
noncomputable section
open scoped BigOperators

/-- Real coefficient columns orthonormal; the vectors need not be orthogonal. -/
theorem coefficient_isometry {Q A E : Type*} [Fintype Q] [Fintype A]
    [DecidableEq A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Q → A → ℝ) (xi : A → E)
    (hC : ∀ a b, ∑ q, C q a * C q b = if a = b then 1 else 0) :
    ∑ q, ‖∑ a, C q a • xi a‖ ^ 2 = ∑ a, ‖xi a‖ ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  calc
    _ = ∑ a, ∑ b, (∑ q, C q a * C q b) * inner ℝ (xi a) (xi b) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by simp [hC]

theorem leading_score_energy {Q A E : Type*} [Fintype Q] [Fintype A]
    [DecidableEq A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Q → A → ℝ) (xi : A → E)
    (hC : ∀ a b, ∑ q, C q a * C q b = if a = b then 1 else 0)
    (epsilon k : ℝ) :
    (∑ q, ‖(1 / (epsilon * k^2)) • (∑ a, C q a • xi a)‖^2) =
      (∑ a, ‖xi a‖^2) / (epsilon^2 * k^4) := by
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [← Finset.mul_sum, coefficient_isometry C xi hC]
  ring

/-- All entropy variables are finite real numbers. Analytic increment bounds are hypotheses. -/
theorem gap_transfer (c eMicro eStar micro0 micro1 star0 star1
    sourceMicro0 sourceMicro1 sourceStar0 sourceStar1 : ℝ)
    (_hc : 0 ≤ c) (_hm : 0 ≤ eMicro) (_hs : 0 ≤ eStar)
    (comparison : micro1 ≤ star1)
    (lower : c * (sourceMicro1 - sourceMicro0) - eMicro ≤ micro1 - micro0)
    (upper : star1 - star0 ≤ c * (sourceStar1 - sourceStar0) + eStar) :
    c * ((sourceStar0 - sourceMicro0) - (sourceStar1 - sourceMicro1))
      - (eMicro + eStar) ≤ star0 - micro0 := by
  linarith

theorem strict_gap (c eMicro eStar micro0 micro1 star0 star1
    sourceMicro0 sourceMicro1 sourceStar0 sourceStar1 : ℝ)
    (hc : 0 < c) (hm : 0 ≤ eMicro) (hs : 0 ≤ eStar)
    (comparison : micro1 ≤ star1)
    (lower : c * (sourceMicro1 - sourceMicro0) - eMicro ≤ micro1 - micro0)
    (upper : star1 - star0 ≤ c * (sourceStar1 - sourceStar0) + eStar)
    (_sourceGap : 0 < sourceStar0 - sourceMicro0)
    (noisyGap : sourceStar1 - sourceMicro1 ≤ (sourceStar0 - sourceMicro0) / 2)
    (errors : eMicro + eStar ≤ c * (sourceStar0 - sourceMicro0) / 2) :
    micro0 < star0 := by
  have h := gap_transfer c eMicro eStar micro0 micro1 star0 star1
    sourceMicro0 sourceMicro1 sourceStar0 sourceStar1 hc.le hm hs comparison lower upper
  nlinarith
end
end T298P
