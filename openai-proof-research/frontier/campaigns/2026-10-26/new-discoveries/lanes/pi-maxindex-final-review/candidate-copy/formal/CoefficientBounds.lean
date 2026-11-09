import Mathlib

open scoped BigOperators

namespace MaxIndex

theorem weighted_coefficient_bound {α : Type*} [Fintype α] [Nonempty α]
    (p c : α → ℝ) (m : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hsmall : ∀ i, p i ≤ 2 / 3)
    (hc : ∀ i, c i ≤ m + 1)
    (hpair : ∀ i j, i ≠ j → c i + c j ≤ m + 5 / 2) :
    (∑ i, c i * p i) ≤ (4 * m + 7) / 6 := by
  classical
  obtain ⟨u, _, hu⟩ := Finset.exists_max_image Finset.univ c Finset.univ_nonempty
  let a := c u
  let b := min a (m + 5 / 2 - a)
  have hca : ∀ i, c i ≤ a := fun i => hu i (Finset.mem_univ i)
  have hab : b ≤ a := min_le_left _ _
  have hab' : a + b ≤ m + 5 / 2 := by
    have := min_le_right a (m + 5 / 2 - a)
    change b ≤ m + 5 / 2 - a at this
    linarith
  have hcb : ∀ i, i ≠ u → c i ≤ b := by
    intro i hi
    apply le_min (hca i)
    have := hpair i u hi
    change c i + a ≤ _ at this
    linarith
  have heach : ∀ i, c i * p i ≤ b * p i + if i = u then (a - b) * p u else 0 := by
    intro i
    by_cases hi : i = u
    · subst i
      simp only [ite_true]
      change a * p u ≤ _
      nlinarith
    · simp only [hi, ite_false, add_zero]
      exact mul_le_mul_of_nonneg_right (hcb i hi) (hp i)
  have hweighted : (∑ i, c i * p i) ≤ b + (a - b) * p u := by
    calc
      (∑ i, c i * p i) ≤ ∑ i, (b * p i + if i = u then (a - b) * p u else 0) :=
        Finset.sum_le_sum (fun i _ => heach i)
      _ = b + (a - b) * p u := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
        simp
  have ha : a ≤ m + 1 := hc u
  have hbnd : (a - b) * p u ≤ (a - b) * (2 / 3) :=
    mul_le_mul_of_nonneg_left (hsmall u) (sub_nonneg.mpr hab)
  linarith

end MaxIndex
