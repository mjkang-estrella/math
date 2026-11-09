import StackSortCut5Count

noncomputable section
namespace StackSort.Cut5
open Seeds2 Shuffle3 Round4 Classical BigOperators

theorem tuples_eq_empty_of_size {M r : ℕ} (hr : M < r) : tuples M r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro F hF
  have hl := (mem_tuples.mp hF).2.1
  have ho := (tuple_output_perm hF).length_eq
  have hb := words_length_le_output (mem_tuples.mp hF).2.2
  simp only [List.length_range] at ho
  omega

theorem XI_eq_zero_of_size {M r s : ℕ} (h : M < r ∨ M < s) : XI M r s = 0 := by
  rcases h with h | h <;> simp [XI,tuples_eq_empty_of_size h]

theorem II_eq_zero_of_size {M r s : ℕ} (h : M < r ∨ M < s) : II M r s = 0 := by
  rcases h with h | h <;> simp [II,tuples_eq_empty_of_size h]

/-- Clipping at 21-M is inactive for supported positive indices in the dependency cone. -/
theorem literalX_eq_XI (M r s : ℕ) (hM : 0 < M) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hr21 : r ≤ 21-M) (hs21 : s ≤ 21-M) : literalX M r s = XI M r s := by
  by_cases h : r ≤ M ∧ s ≤ M
  · have hb : 1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M := by unfold bound; omega
    simp [literalX,show M ≠ 0 by omega,hb]
  · have hz : M < r ∨ M < s := by omega
    have hb : ¬ (1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M) := by unfold bound; omega
    simp [literalX,show M ≠ 0 by omega,hb,XI_eq_zero_of_size hz]

theorem literalI_eq_II (M r s : ℕ) (hM : 0 < M) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hr21 : r ≤ 21-M) (hs21 : s ≤ 21-M) : literalI M r s = II M r s := by
  by_cases h : r ≤ M ∧ s ≤ M
  · have hb : 1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M := by unfold bound; omega
    simp [literalI,show M ≠ 0 by omega,hb]
  · have hz : M < r ∨ M < s := by omega
    have hb : ¬ (1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M) := by unfold bound; omega
    simp [literalI,show M ≠ 0 by omega,hb,II_eq_zero_of_size hz]

/-- The exact frozen correction is the unrestricted common-cut sum on its bound. -/
theorem correction_eq_raw (M r s : ℕ) (hr : 1 ≤ r) (hrB : r ≤ bound M)
    (_hs : 1 ≤ s) (hsB : s ≤ bound M) :
    correction false literalX literalI M r s =
      ∑ b ∈ Finset.Ico 1 M, ∑ a ∈ Finset.Ico 1 r, ∑ c ∈ Finset.Ico 1 s,
        Nat.choose M b * (XI (M-b) (r-a) (s-c) * II b a c) := by
  unfold correction convolution
  simp only [Bool.false_eq_true,ite_false]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hb := Finset.mem_Ico.mp hb
  have ha := Finset.mem_Ico.mp ha
  have hc := Finset.mem_Ico.mp hc
  have hr21 : r ≤ 21-M := (Nat.le_min.mp hrB).2
  have hs21 : s ≤ 21-M := (Nat.le_min.mp hsB).2
  have hM21 : M ≤ 20 := by omega
  rw [literalX_eq_XI (M-b) (r-a) (s-c) (by omega) (by omega) (by omega)
      (by omega) (by omega),
    literalI_eq_II b a c (by omega) (by omega) (by omega) (by omega) (by omega)]

end StackSort.Cut5
