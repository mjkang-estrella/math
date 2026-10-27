import ErrorSeries
noncomputable section
namespace EulerTuran
def positiveTerm (n k : ℕ) : ℝ := (1 / (2*(k:ℝ)+3))^(n+2)
def positiveError (n : ℕ) : ℝ := ∑' k, positiveTerm n k
lemma positiveTerm_pos (n k : ℕ) : 0 < positiveTerm n k := by
  dsimp [positiveTerm]
  positivity
lemma positiveError_summable_bound (n : ℕ) :
    Summable (positiveTerm n) ∧ positiveError n ≤ 1/2 := by
  have hh := summable_of_telescope_bound (fun k => (positiveTerm_pos n k).le)
    (u := fun k => 1 / ((k:ℝ)+2)) (fun k => by positivity) ?_
  · simpa [positiveError] using hh
  · intro k
    have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    have hbase : 1 / (2*(k:ℝ)+3) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith
    have hp : positiveTerm n k ≤ (1 / (2*(k:ℝ)+3))^2 := by
      exact pow_le_pow_of_le_one (by positivity) hbase (by omega)
    have hpoly : ((k:ℝ)+2)*((k:ℝ)+3) ≤ (2*(k:ℝ)+3)^2 := by nlinarith
    have hden : 0 < ((k:ℝ)+2)*((k:ℝ)+3) := by positivity
    have hsq : (1 / (2*(k:ℝ)+3))^2 ≤
        1 / (((k:ℝ)+2)*((k:ℝ)+3)) := by
      rw [div_pow, one_pow]
      exact one_div_le_one_div_of_le hden hpoly
    have heq : 1 / (((k:ℝ)+2)*((k:ℝ)+3)) =
        1 / ((k:ℝ)+2) - 1 / (((k+1:ℕ):ℝ)+2) := by
      push_cast
      field_simp
      ring
    exact hp.trans (hsq.trans_eq heq)
lemma positiveError_bounds (n : ℕ) : 0 < positiveError n ∧ positiveError n < 1 := by
  have hs := (positiveError_summable_bound n).1
  have hp : 0 < positiveError n := lt_of_lt_of_le (positiveTerm_pos n 0)
    (hs.le_tsum 0 (fun k _ => (positiveTerm_pos n k).le))
  exact ⟨hp, lt_of_le_of_lt (positiveError_summable_bound n).2 (by norm_num)⟩
lemma positiveError_contraction (n : ℕ) : positiveError (n+2) ≤ positiveError n/3 := by
  have hh : ∀ k, positiveTerm (n+2) k ≤ positiveTerm n k/3 := by
    intro k
    have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    have hb : 0 ≤ 1 / (2*(k:ℝ)+3) := by positivity
    have hu : 1 / (2*(k:ℝ)+3) ≤ 1/3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    have hs : (1 / (2*(k:ℝ)+3))^2 ≤ (1/3:ℝ) := by
      nlinarith [sq_nonneg (1 / (2*(k:ℝ)+3) - 1/3)]
    have hp : 0 ≤ (1 / (2*(k:ℝ)+3))^(n+2) := by positivity
    dsimp [positiveTerm]
    rw [show n+2+2 = n+2+2 by rfl, pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hs hp]
  have h := Summable.tsum_le_tsum hh (positiveError_summable_bound (n+2)).1
    ((positiveError_summable_bound n).1.div_const 3)
  simpa [positiveError, tsum_div_const] using h
end EulerTuran
