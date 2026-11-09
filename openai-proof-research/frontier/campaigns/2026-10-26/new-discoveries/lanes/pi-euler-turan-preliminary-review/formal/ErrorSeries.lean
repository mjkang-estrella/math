import AlternatingCriterion
noncomputable section
open scoped BigOperators
namespace EulerTuran
lemma sum_telescope (u : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (u k - u (k+1)) = u 0 - u N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring
lemma summable_of_telescope_bound {f u : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hu : ∀ k, 0 ≤ u k)
    (hb : ∀ k, f k ≤ u k-u (k+1)) :
    Summable f ∧ ∑' k, f k ≤ u 0 := by
  have hh : ∀ N, ∑ k ∈ Finset.range N, f k ≤ u 0 := by
    intro N
    calc
      _ ≤ ∑ k ∈ Finset.range N, (u k-u (k+1)) := Finset.sum_le_sum fun k _ => hb k
      _ = u 0-u N := sum_telescope u N
      _ ≤ u 0 := sub_le_self _ (hu N)
  exact ⟨summable_of_sum_range_le hf hh, Real.tsum_le_of_sum_range_le hf hh⟩
def evenTerm (n k : ℕ) : ℝ :=
  (1/(4*(k:ℝ)+3))^(n+1) - (1/(4*(k:ℝ)+5))^(n+1)
def evenError (n : ℕ) : ℝ := ∑' k, evenTerm n k
lemma evenTerm_nonneg (n k : ℕ) : 0 ≤ evenTerm n k := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  dsimp [evenTerm]
  apply sub_nonneg.mpr
  apply pow_le_pow_left₀ (by positivity)
  apply one_div_le_one_div_of_le (by positivity)
  linarith
lemma evenTerm_pos_zero (n : ℕ) : 0 < evenTerm n 0 := by
  dsimp [evenTerm]
  norm_num only [Nat.cast_zero, mul_zero, zero_add]
  apply sub_pos.mpr
  exact pow_lt_pow_left₀ (by norm_num : (1/5:ℝ)<1/3) (by norm_num) (by omega)
lemma evenError_summable_bound (n : ℕ) :
    Summable (evenTerm n) ∧ evenError n ≤ (1/3:ℝ)^(n+1) := by
  have h := summable_of_telescope_bound (evenTerm_nonneg n)
    (u := fun k => (1/(4*(k:ℝ)+3))^(n+1)) (fun k => by positivity) ?_
  · simpa [evenError] using h
  · intro k
    dsimp [evenTerm]
    apply sub_le_sub_left
    apply pow_le_pow_left₀ (by positivity)
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
lemma evenError_bounds (n : ℕ) : 0 < evenError n ∧ evenError n < 1 := by
  have hs := (evenError_summable_bound n).1
  have hp : 0 < evenError n :=
    lt_of_lt_of_le (evenTerm_pos_zero n) (hs.le_tsum 0 (fun k _ => evenTerm_nonneg n k))
  have hu := (evenError_summable_bound n).2
  have hpow : (1/3:ℝ)^(n+1) ≤ 1/3 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)≤1) (by omega : 1≤n+1)
  exact ⟨hp, by linarith⟩
lemma evenError_contraction (n : ℕ) : evenError (n+2) ≤ evenError n/3 := by
  have hh : ∀ k, evenTerm (n+2) k ≤ evenTerm n k/3 := by
    intro k
    have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    simpa [evenTerm, Nat.add_assoc] using paired_power_contraction
      (A := 1/(4*(k:ℝ)+3)) (B := 1/(4*(k:ℝ)+5)) (by positivity)
      (one_div_le_one_div_of_le (by positivity) (by linarith))
      ((div_le_iff₀ (by positivity : (0:ℝ)<4*(k:ℝ)+3)).2 (by linarith)) n
  have h := Summable.tsum_le_tsum hh (evenError_summable_bound (n+2)).1
    ((evenError_summable_bound n).1.div_const 3)
  simpa [evenError, tsum_div_const] using h
end EulerTuran
