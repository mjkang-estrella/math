import OddError
noncomputable section
namespace EulerTuran
/-- The zeroth coefficient is handled directly, avoiding a conditional series. -/
def sourceError (n : ℕ) : ℝ :=
  if n = 0 then 1-Real.pi/4 else if Even n then evenError n else positiveError (n-1)
lemma sourceError_bounds (n : ℕ) : 0 < sourceError n ∧ sourceError n < 1 := by
  unfold sourceError
  split_ifs with hn he
  · constructor <;> linarith [Real.pi_lt_four, Real.pi_pos]
  · exact evenError_bounds n
  · exact positiveError_bounds (n-1)
lemma sourceError_contraction (n : ℕ) : sourceError (n+2) ≤ sourceError n/3 := by
  by_cases hn : n = 0
  · subst n
    have hh := (evenError_summable_bound 2).2
    norm_num at hh
    simp only [sourceError, show (0+2:ℕ) ≠ 0 by omega, ite_false,
      show Even (0+2:ℕ) by decide, ite_true]
    nlinarith [Real.pi_lt_d2]
  · have hn2 : n+2 ≠ 0 := by omega
    have he : Even (n+2) ↔ Even n := by simp only [Nat.even_iff]; omega
    simp only [sourceError, hn, hn2, ite_false, he]
    split_ifs with h
    · exact evenError_contraction n
    · have hh := positiveError_contraction (n-1)
      have hi : n+2-1 = n-1+2 := by omega
      simpa [hi] using hh
theorem sourceError_turan (n j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    0 < (-1:ℝ)^(n+1) * (corrected sourceError n * corrected sourceError (n+j+k) -
      corrected sourceError (n+j) * corrected sourceError (n+k)) :=
  alternating_turan_of_contraction sourceError_bounds sourceError_contraction n j k hj hk
end EulerTuran
