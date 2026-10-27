import Mathlib

namespace Davis

theorem finite_flux (d : ℕ) (L M f : ℕ → ℝ)
    (hL : L d = 0) (hM : M 0 = 0) (hbalance : ∀ i < d, L i = M (i + 1)) :
    (∑ i ∈ Finset.range (d + 1), L i * (f (i + 1) - f i)) =
      ∑ i ∈ Finset.range (d + 1), M i * (f i - f (i - 1)) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [hL, hM, zero_mul, add_zero, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hbalance i (Finset.mem_range.mp hi)]

theorem finite_stationarity (d : ℕ) (L M f : ℕ → ℝ)
    (hL : L d = 0) (hM : M 0 = 0) (hbalance : ∀ i < d, L i = M (i + 1)) :
    (∑ i ∈ Finset.range (d + 1),
      (L i * (f (i + 1) - f i) + M i * (f (i - 1) - f i))) = 0 := by
  have h := finite_flux d L M f hL hM hbalance
  calc
    _ = (∑ i ∈ Finset.range (d + 1), L i * (f (i + 1) - f i)) -
        ∑ i ∈ Finset.range (d + 1), M i * (f i - f (i - 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := sub_eq_zero.mpr h

end Davis
