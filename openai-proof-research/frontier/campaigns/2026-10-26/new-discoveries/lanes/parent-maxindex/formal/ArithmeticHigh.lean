import ProbabilityEntries

open scoped BigOperators

namespace MaxIndex

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem arithmetic_high_pointwise (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (u : α) (hu : 2 / 3 < p u) (e : α × α) :
    arithmeticEntry p e ≤ p u / 2 + (if e = (u, u) then p u / 2 else 0) +
      (if e.1 = u ∧ e.2 ≠ u then p e.2 / 2 else 0) +
      (if e.2 = u ∧ e.1 ≠ u then p e.1 / 2 else 0) := by
  rcases e with ⟨x, y⟩
  by_cases hx : x = u <;> by_cases hy : y = u
  · subst x; subst y
    simp [arithmeticEntry]
  · subst x
    simp [arithmeticEntry, hy, add_div]
  · subst y
    simp [arithmeticEntry, hx, add_div, add_comm]
  · have hxt := probability_tail_le p hp hsum u x hx
    have hyt := probability_tail_le p hp hsum u y hy
    simp only [arithmeticEntry, hx, hy, Prod.mk.injEq, false_and, ite_false,
      and_false, add_zero]
    linarith

theorem arithmetic_high_sum (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (u : α) (hu : 2 / 3 < p u)
    (m : ℕ) (s : Finset (α × α)) (hs : s.card ≤ 2 * m + 1) :
    (∑ e ∈ s, arithmeticEntry p e) ≤ 1 + (m : ℝ) * p u := by
  have hloop : (∑ e ∈ s, if e = (u, u) then p u / 2 else 0) ≤ p u / 2 := by
    simp only [Finset.sum_ite_eq']
    split_ifs <;> linarith [hp u]
  have hrow0 : ∀ e : α × α,
      0 ≤ if e.1 = u ∧ e.2 ≠ u then p e.2 / 2 else 0 := by
    intro e; split_ifs
    · exact div_nonneg (hp _) (by norm_num)
    · exact le_rfl
  have hcol0 : ∀ e : α × α,
      0 ≤ if e.2 = u ∧ e.1 ≠ u then p e.1 / 2 else 0 := by
    intro e; split_ifs
    · exact div_nonneg (hp _) (by norm_num)
    · exact le_rfl
  have hrowFull : (∑ e : α × α, if e.1 = u ∧ e.2 ≠ u then p e.2 / 2 else 0) =
      (1 - p u) / 2 := by
    rw [Fintype.sum_prod_type]
    simp only [ite_and, Finset.sum_ite_irrel]
    simp [← Finset.sum_div, Finset.sum_ite, Finset.filter_ne',
      Finset.sum_erase_eq_sub, hsum]
  have hcolFull : (∑ e : α × α, if e.2 = u ∧ e.1 ≠ u then p e.1 / 2 else 0) =
      (1 - p u) / 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [ite_and]
    simp only [← ite_and]
    simpa only [Fintype.sum_prod_type] using hrowFull
  have hrow : (∑ e ∈ s, if e.1 = u ∧ e.2 ≠ u then p e.2 / 2 else 0) ≤
      (1 - p u) / 2 := by
    rw [← hrowFull]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun e _ _ => hrow0 e)
  have hcol : (∑ e ∈ s, if e.2 = u ∧ e.1 ≠ u then p e.1 / 2 else 0) ≤
      (1 - p u) / 2 := by
    rw [← hcolFull]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun e _ _ => hcol0 e)
  have hpoint := Finset.sum_le_sum (s := s)
    (fun e _ => arithmetic_high_pointwise p hp hsum u hu e)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hpoint
  have hcard : (s.card : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hs
  have hbase := mul_le_mul_of_nonneg_right hcard (show 0 ≤ p u / 2 by positivity)
  linarith

end MaxIndex
