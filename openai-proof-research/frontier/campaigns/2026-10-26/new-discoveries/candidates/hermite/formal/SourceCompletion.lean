import OddAssembly

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

/-- Source assembly only: the odd bulk premise is still explicit at this checkpoint. -/
theorem source_conjecture_of_odd_bulk
    (hb : ∀ m : ℕ, 1 ≤ m → ∀ x : ℝ, 0 ≤ x →
      x ^ 2 < 2 * ((2 * m + 1 : ℕ) : ℝ) + 1 →
      |weightedHermite (2 * m + 1) x| ≤
        sourceCoefficient (2 * m + 1) * sourceEnvelope (2 * m + 1) x) :
    SourceConjecture346243 := by
  intro n hn x hx
  apply source_point_of_weighted
  apply weighted_clamped_of_bulk n hn ?_ x hx.le
  intro t ht hq
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp he
    exact source_bulk_even m t ht hq
  · obtain ⟨m, rfl⟩ := odd_iff_exists_bit1.mp ho
    by_cases hm : m = 0
    · subst m
      norm_num at hq ⊢
      exact source_bulk_one t hq
    · exact hb m (by omega) t ht hq

end HermiteEnvelope
