import RCS128

/- Copyright (c) 2026 Myeongjin Kang. MIT. Hypothesis-sensitivity controls. -/
namespace RCS128Controls

/-- Even total layer count alone is not phase-specific parity. -/
theorem even_total_does_not_pair_threshold :
    Even (2 : ℕ) ∧ (2 : ℤ) ≤ 2 ∧ ¬ ((2 : ℤ) ≤ 1) := by
  norm_num

/-- Even cardinality without downward closure can split the first pair. -/
theorem unordered_even_set_splits_pair :
    Even ({0, 2} : Finset ℕ).card ∧ 0 ∈ ({0, 2} : Finset ℕ) ∧
      1 ∉ ({0, 2} : Finset ℕ) := by
  decide

/-- An odd initial segment can end between adjacent pair members. -/
theorem odd_tail_splits_pair :
    (Finset.range 1).card = 1 ∧ 0 ∈ Finset.range 1 ∧ 1 ∉ Finset.range 1 := by
  decide

/-- A reflection with a fixed point does not force even cardinality. -/
theorem fixed_point_has_odd_card :
    (∀ x ∈ ({0} : Finset ℕ), id (id x) = x) ∧
      ¬ Even ({0} : Finset ℕ).card := by
  norm_num

/-- Exactly `2*k` records do not force an outside record. -/
theorem no_outside_at_equal_cap :
    (Finset.range 2).card = 2 ∧
      ¬ ∃ x ∈ Finset.range 2, x ∉ Finset.range 2 := by
  simp

/-- A positive deficit without parity is insufficient for the fixed-word bound. -/
theorem positive_odd_deficit_fails :
    0 < (1 : ℕ) ∧ ¬ ((2 : ℕ) * 1 + 1 ≤ 1 * (1 + 1)) := by
  decide

/-- Forgetting the half-Euler step leaves room for factor four. -/
theorem unhalved_cost_can_exceed_factor_two :
    (4 : ℕ) ≤ 2 * 2 ∧ (2 : ℕ) ≤ 2 * 1 ∧ ¬ (4 : ℕ) ≤ 2 * 1 := by
  decide

end RCS128Controls
