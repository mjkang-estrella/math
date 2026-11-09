import ArithmeticHigh
import SortedBridge
import ScalarBounds

open scoped BigOperators

namespace MaxIndex

theorem universal_mask_bound {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (m : ℕ) (hk : 2 * m + 1 ≤ Fintype.card (α × α)) :
    maskTopSum (arithmeticEntry p) (2 * m + 1) +
      maskTopSum (geometricEntry p) (2 * m + 1) < (m : ℝ) + 3 := by
  classical
  obtain ⟨u, _, hu⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  have humax : ∀ i, p i ≤ p u := fun i => hu i (Finset.mem_univ i)
  by_cases hsmall : p u ≤ 2 / 3
  · have ha : maskTopSum (arithmeticEntry p) (2 * m + 1) ≤
        (4 * (m : ℝ) + 7) / 6 := by
      apply maskTopSum_le
      intro s hs
      exact arithmetic_low_maximum p hp hsum (fun i => (humax i).trans hsmall) m s hs
    have hg := geometric_low_bound p hp hsum (2 * m + 1)
    have hscalar := low_maximum_bound (m : ℝ) (by positivity)
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hg
    exact lt_of_le_of_lt (add_le_add ha hg) hscalar
  · have hlarge : 2 / 3 < p u := lt_of_not_ge hsmall
    have ha : maskTopSum (arithmeticEntry p) (2 * m + 1) ≤
        1 + (m : ℝ) * p u := by
      apply maskTopSum_le
      intro s hs
      exact arithmetic_high_sum p hp hsum u hlarge m s hs
    have hg := geometric_high_bound p hp hsum u humax m hk
    have hscalar := high_maximum_bound (m : ℝ) (p u) (by positivity)
      (hp u) (probability_le_one p hp hsum u)
    linarith

/-- The actual separately sorted arithmetic and geometric entry arrays satisfy
the conjectured index bound in every dimension at least three. Maximality is
a separate theorem and is not asserted here. -/
theorem source_universal_index (d : ℕ) (hd : 3 ≤ d) (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    sortedTopSum (arithmeticEntry p) (2 * d - 5) +
      sortedTopSum (geometricEntry p) (2 * d - 5) < (d : ℝ) := by
  let m := d - 3
  have hdm : d = m + 3 := by dsimp [m]; omega
  have hk : 2 * m + 1 ≤ Fintype.card (Fin d × Fin d) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  have hk' : 2 * d - 5 = 2 * m + 1 := by omega
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  rw [hk', sortedTopSum_eq_maskTopSum _ (fun e => by
    exact div_nonneg (add_nonneg (hp e.1) (hp e.2)) (by norm_num)) _ hk,
    sortedTopSum_eq_maskTopSum _ (geometricEntry_nonneg p) _ hk]
  have h := universal_mask_bound p hp hsum m hk
  have hdreal : (d : ℝ) = (m : ℝ) + 3 := by exact_mod_cast hdm
  linarith

end MaxIndex
