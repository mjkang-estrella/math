import EulerCoefficient
import BilateralSeries
noncomputable section
namespace EulerTuran
lemma normalizedEuler_bilateral {n : ℕ} (hn : 1 ≤ n) :
    normalizedEuler n = 2*(2/Real.pi)^(n+1)*bilateral n := by
  have he (m : ℤ) : 1 / ((1/4:ℝ)+m)^(n+1) =
      (4:ℝ)^(n+1) * (1/(4*(m:ℝ)+1))^(n+1) := by
    rw [show (1/4:ℝ)+m = (4*(m:ℝ)+1)/4 by ring, div_pow]
    simp only [one_div_div, div_pow, one_pow]
    ring
  rw [normalizedEuler_shifted_series hn]
  simp_rw [he]
  rw [tsum_mul_left]
  change (4:ℝ)^(n+1) * bilateral n / (2^n * Real.pi^(n+1)) = _
  rw [div_pow, show (4:ℝ)^(n+1) = (2:ℝ)^(n+1)*(2:ℝ)^(n+1) by
    rw [← mul_pow]; norm_num, pow_succ]
  field
lemma bilateral_corrected {n : ℕ} (hn : 1 ≤ n) : bilateral n = corrected sourceError n := by
  have hn0 : n ≠ 0 := by omega
  rcases Nat.even_or_odd n with he | ho
  · rw [bilateral_even hn he]
    simp only [corrected, sourceError, hn0, ite_false, he, ite_true,
      pow_add, he.neg_one_pow, pow_one, one_mul, neg_one_mul]
    ring
  · rw [bilateral_odd hn ho]
    have he : ¬ Even n := Nat.not_even_iff_odd.mpr ho
    simp only [corrected, sourceError, hn0, ite_false, he,
      pow_add, ho.neg_one_pow, pow_one, neg_mul_neg, one_mul]
lemma normalizedEuler_corrected (n : ℕ) :
    normalizedEuler n = 2*(2/Real.pi)^(n+1)*corrected sourceError n := by
  by_cases hn : n = 0
  · subst n
    rw [normalizedEuler_zero]
    norm_num [corrected, sourceError]
    field_simp
    ring
  · exact (normalizedEuler_bilateral (by omega : 1 ≤ n)).trans
      (congrArg (fun x : ℝ => 2*(2/Real.pi)^(n+1)*x) (bilateral_corrected (by omega)))
/-- Full all-index sign assertion on actual secant-plus-tangent Taylor coefficients. -/
theorem source_conjecture_338918 (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    0 < (-1:ℝ)^(n+1) *
      (normalizedEuler n * normalizedEuler (n+j+k) -
        normalizedEuler (n+j) * normalizedEuler (n+k)) := by
  have hh := sourceError_turan n j k (by omega) (by omega)
  have hr : 0 < (2:ℝ)/Real.pi := by positivity
  have hp : 0 < 4*((2:ℝ)/Real.pi)^(n+1)*((2:ℝ)/Real.pi)^(n+j+k+1) := by positivity
  have h := mul_pos hp hh
  rw [normalizedEuler_corrected, normalizedEuler_corrected,
    normalizedEuler_corrected, normalizedEuler_corrected]
  convert h using 1
  simp only [pow_add, pow_one]
  ring
end EulerTuran
