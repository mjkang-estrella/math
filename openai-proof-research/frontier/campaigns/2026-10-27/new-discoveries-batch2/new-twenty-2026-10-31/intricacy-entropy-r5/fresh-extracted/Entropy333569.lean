import Diagonal333569

namespace MathDB333569
noncomputable section
open Set

/-- The conditional entropy of the binary transition matrix in the chart. -/
def conditionalEntropy (r t : ℝ) : ℝ :=
  (1+t)/2 * Real.binEntropy ((1-r)/2*(1-t)) +
  (1-t)/2 * Real.binEntropy ((1-r)/2*(1+t))

theorem conditionalEntropy_even (r t : ℝ) :
    conditionalEntropy r (-t) = conditionalEntropy r t := by
  simp only [conditionalEntropy, ← sub_eq_add_neg, sub_neg_eq_add]
  ring

theorem conditionalEntropy_zero (r : ℝ) : conditionalEntropy r 0 = gapEntropy r := by
  simp only [conditionalEntropy, add_zero, sub_zero, mul_one, gapEntropy]
  ring

theorem entropyArgs_mem {r t : ℝ} (hr : r ∈ Icc 0 1) (ht : t ∈ Icc (-1) 1) :
    (1-r)/2*(1-t) ∈ Icc (0:ℝ) 1 ∧ (1-r)/2*(1+t) ∈ Icc (0:ℝ) 1 := by
  have h0 : 0 ≤ 1-r := by linarith [hr.2]
  have h1 : 0 ≤ 1-t := by linarith [ht.2]
  have h2 : 0 ≤ 1+t := by linarith [ht.1]
  constructor
  · constructor
    · positivity
    · nlinarith [mul_nonneg hr.1 h1]
  · constructor
    · positivity
    · nlinarith [mul_nonneg hr.1 h2]

theorem conditionalEntropy_nonneg {r t : ℝ} (hr : r ∈ Icc 0 1)
    (ht : t ∈ Icc (-1) 1) : 0 ≤ conditionalEntropy r t := by
  obtain ⟨ha, hb⟩ := entropyArgs_mem hr ht
  exact add_nonneg
    (mul_nonneg (by linarith [ht.1]) (Real.binEntropy_nonneg ha.1 ha.2))
    (mul_nonneg (by linarith [ht.2]) (Real.binEntropy_nonneg hb.1 hb.2))

theorem conditionalEntropy_le {r t : ℝ} (ht : t ∈ Icc (-1) 1) :
    conditionalEntropy r t ≤ Real.log 2 := by
  have h1 := mul_le_mul_of_nonneg_left (Real.binEntropy_le_log_two (p := (1-r)/2*(1-t)))
    (show 0 ≤ (1+t)/2 by linarith [ht.1])
  have h2 := mul_le_mul_of_nonneg_left (Real.binEntropy_le_log_two (p := (1-r)/2*(1+t)))
    (show 0 ≤ (1-t)/2 by linarith [ht.2])
  unfold conditionalEntropy
  nlinarith

/-- Uniform geometric domination of the conditional-entropy gap series. -/
theorem conditionalEntropySeries_summable {l t : ℝ} (hl : l ∈ Icc 0 1)
    (ht : t ∈ Icc (-1) 1) :
    Summable (fun n : ℕ => (1/2:ℝ)^(n+1)*conditionalEntropy (l^(n+1)) t) := by
  apply geometricMajorant_summable.of_norm_bounded
  intro n
  have he := conditionalEntropy_nonneg
    (show l^(n+1) ∈ Icc (0:ℝ) 1 from ⟨pow_nonneg hl.1 _, pow_le_one₀ hl.1 hl.2⟩) ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) he)]
  exact mul_le_mul_of_nonneg_left (conditionalEntropy_le ht) (by positivity)

#print axioms conditionalEntropy_even
#print axioms conditionalEntropy_zero
#print axioms conditionalEntropySeries_summable
end
end MathDB333569
