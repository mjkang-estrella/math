import MeanSufficiency
import MeanNecessity

open Set Real
namespace ClassicalMeanRange

def SourceComparison (n x y : ℝ) : Prop :=
  (arithmetic x y) ^ n + (geometric x y) ^ n ≤
    (quadratic x y) ^ n + (harmonic x y) ^ n

def UniversallyValid (n : ℝ) : Prop :=
  ∀ (x y : ℝ), 0 < x → 0 < y → SourceComparison n x y

lemma normalizedDefect_eq_source (n : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    (quadratic (pairLeft c) (pairRight c)) ^ n +
        (harmonic (pairLeft c) (pairRight c)) ^ n -
        (arithmetic (pairLeft c) (pairRight c)) ^ n -
        (geometric (pairLeft c) (pairRight c)) ^ n = normalizedDefect n c := by
  rcases normalized_pair hc with ⟨_, _, ha, hg, hh, hq⟩
  rw [ha, hg, hh, hq, Real.one_rpow]
  have hbase : 0 ≤ 2 * c ^ 2 - 1 := by nlinarith
  have hc0 : 0 ≤ c := by linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase]
  rw [show (1 / 2 : ℝ) * n = n / 2 by ring]
  rw [one_div, Real.inv_rpow hc0, ← Real.rpow_neg hc0]
  rfl

/-- Every exponent in (0,1) admits strictly positive actual inputs refuting the comparison. -/
theorem source_failure_all_intermediate {n : ℝ} (hn0 : 0 < n) (hn1 : n < 1) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ ¬ SourceComparison n x y := by
  obtain ⟨c, hc, hf⟩ := exists_normalized_failure hn0 hn1
  have hp := normalized_pair hc.le
  refine ⟨pairLeft c, pairRight c, hp.1, hp.2.1, ?_⟩
  intro h
  have he := normalizedDefect_eq_source n hc.le
  unfold SourceComparison at h
  linarith

/-- Exact source exponent classification: n≤0 or n≥1, correcting the proposed 1/2 boundary. -/
theorem source_exponent_classification (n : ℝ) :
    UniversallyValid n ↔ n ≤ 0 ∨ 1 ≤ n := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨x,y,hx,hy,hf⟩ := source_failure_all_intermediate hn.1 hn.2
    exact hf (h x y hx hy)
  · intro hn x y hx hy
    rcases hn with hn | hn
    · exact source_inequality_nonpos hn hx hy
    · exact source_inequality_ge_one hn hx hy

/-- A compact algebraic witness at the source's asserted half-power boundary. -/
theorem explicit_half_power_failure :
    ¬ SourceComparison (1 / 2) (4 + Real.sqrt 15) (4 - Real.sqrt 15) := by
  have hp := normalized_pair (by norm_num : (1 : ℝ) ≤ 4)
  norm_num [pairLeft, pairRight] at hp
  have ha : arithmetic (4 + Real.sqrt 15) (4 - Real.sqrt 15) = 4 := by
    simpa using hp.2.2.1
  have hg : geometric (4 + Real.sqrt 15) (4 - Real.sqrt 15) = 1 := by
    simpa using hp.2.2.2.1
  have hh : harmonic (4 + Real.sqrt 15) (4 - Real.sqrt 15) = 1 / 4 := by
    simpa using hp.2.2.2.2.1
  have hq : quadratic (4 + Real.sqrt 15) (4 - Real.sqrt 15) = Real.sqrt 31 := by
    simpa using hp.2.2.2.2.2
  intro h
  unfold SourceComparison at h
  rw [ha, hg, hh, hq] at h
  simp only [← Real.sqrt_eq_rpow] at h
  norm_num at h
  have hs31 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 31)
  have hs31pos := Real.sqrt_nonneg (31 : ℝ)
  have hss := Real.sq_sqrt hs31pos
  have hsspos := Real.sqrt_nonneg (Real.sqrt (31 : ℝ))
  have hslt : Real.sqrt (31 : ℝ) < 25 / 4 := by nlinarith
  have hsslt : Real.sqrt (Real.sqrt (31 : ℝ)) < 5 / 2 := by nlinarith
  linarith

end ClassicalMeanRange
