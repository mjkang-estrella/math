import ShoeTV

namespace Shoe
open MeasureTheory
open scoped ENNReal

noncomputable def positiveDifference (p q : PMF ℕ) (i : ℕ) : ℝ :=
  max ((p i).toReal-(q i).toReal) 0

theorem positiveDifference_summable (p q : PMF ℕ) : Summable (positiveDifference p q) := by
  apply Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
    (fun i => ?_) (tv_absolute_summable p q)
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem countableTV_positive (p q : PMF ℕ) :
    countableTV p q = ∑' i, positiveDifference p q i := by
  have he (i : ℕ) : positiveDifference p q i =
      (|(p i).toReal-(q i).toReal| + ((p i).toReal-(q i).toReal))/2 := by
    unfold positiveDifference
    rcases le_total ((p i).toReal-(q i).toReal) 0 with h | h
    · rw [max_eq_right h,abs_of_nonpos h]; ring
    · rw [max_eq_left h,abs_of_nonneg h]; ring
  simp_rw [he]
  rw [((tv_absolute_summable p q).add ((pmf_real_summable p).sub
    (pmf_real_summable q))).hasSum.div_const 2 |>.tsum_eq,
    (tv_absolute_summable p q).tsum_add ((pmf_real_summable p).sub (pmf_real_summable q)),
    (pmf_real_summable p).tsum_sub (pmf_real_summable q), pmf_real_sum, pmf_real_sum]
  simp [countableTV]

theorem pmf_subset_real (p : PMF ℕ) (A : Set ℕ) :
    (p.toMeasure A).toReal = ∑' i, A.indicator (fun i => (p i).toReal) i := by
  classical
  rw [p.toMeasure_apply (Set.to_countable A).measurableSet,
    ENNReal.tsum_toReal_eq (by
      intro i; by_cases hi : i ∈ A
      · simp only [Set.indicator_of_mem hi]
        exact ne_of_lt (lt_of_le_of_lt (p.coe_le_one i) ENNReal.one_lt_top)
      · simp [Set.indicator_of_notMem hi])]
  apply tsum_congr
  intro i
  by_cases hi : i ∈ A <;> simp [hi]

theorem subset_difference (p q : PMF ℕ) (A : Set ℕ) :
    (p.toMeasure A).toReal-(q.toMeasure A).toReal =
      ∑' i, A.indicator (fun i => (p i).toReal-(q i).toReal) i := by
  classical
  rw [pmf_subset_real,pmf_subset_real,
    ← ((pmf_real_summable p).indicator A).tsum_sub ((pmf_real_summable q).indicator A)]
  apply tsum_congr
  intro i
  by_cases hi : i ∈ A <;> simp [hi]

theorem subset_difference_le (p q : PMF ℕ) (A : Set ℕ) :
    (p.toMeasure A).toReal-(q.toMeasure A).toReal ≤ countableTV p q := by
  classical
  rw [subset_difference,countableTV_positive]
  apply (((pmf_real_summable p).sub (pmf_real_summable q)).indicator A).tsum_le_tsum
    _ (positiveDifference_summable p q)
  intro i
  by_cases hi : i ∈ A
  · simpa only [Set.indicator_of_mem hi, positiveDifference] using le_max_left
      ((p i).toReal-(q i).toReal) 0
  · simpa only [Set.indicator_of_notMem hi, positiveDifference] using le_max_right
      ((p i).toReal-(q i).toReal) 0

theorem countableTV_symm (p q : PMF ℕ) : countableTV p q = countableTV q p := by
  unfold countableTV
  congr 1
  apply tsum_congr
  intro i
  exact abs_sub_comm _ _

theorem source_subset_bound (p q : PMF ℕ) (A : Set ℕ) :
    |(p.toMeasure A).toReal-(q.toMeasure A).toReal| ≤ countableTV p q := by
  apply abs_le.mpr
  constructor
  · have h := subset_difference_le q p A
    rw [← countableTV_symm p q] at h
    linarith
  · exact subset_difference_le p q A

theorem positive_subset_attains (p q : PMF ℕ) :
    |(p.toMeasure {i | (q i).toReal ≤ (p i).toReal}).toReal -
      (q.toMeasure {i | (q i).toReal ≤ (p i).toReal}).toReal| = countableTV p q := by
  classical
  rw [subset_difference]
  have he (i : ℕ) : ({i | (q i).toReal ≤ (p i).toReal} : Set ℕ).indicator
      (fun i => (p i).toReal-(q i).toReal) i = positiveDifference p q i := by
    by_cases h : (q i).toReal ≤ (p i).toReal
    · simp [h,positiveDifference]
    · simp [h,positiveDifference,max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
  simp_rw [he]
  rw [abs_of_nonneg (tsum_nonneg (fun _ => le_max_right _ _)),← countableTV_positive]

noncomputable def sourceTV (p q : PMF ℕ) : ℝ :=
  sSup (Set.range (fun A : Set ℕ => |(p.toMeasure A).toReal-(q.toMeasure A).toReal|))

theorem sourceTV_eq_countableTV (p q : PMF ℕ) : sourceTV p q = countableTV p q := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨A,rfl⟩
    exact source_subset_bound p q A
  · rw [← positive_subset_attains p q]
    apply le_csSup
    · exact ⟨countableTV p q, by rintro _ ⟨A,rfl⟩; exact source_subset_bound p q A⟩
    · exact ⟨_,rfl⟩

theorem source_discrepancy_uniform (p : DiscreteLaw ℕ) :
    sourceTV (pairLaw p) (winningLaw p) ≤ 255/256 := by
  rw [sourceTV_eq_countableTV]
  exact discrepancy_uniform_bound p

end Shoe
