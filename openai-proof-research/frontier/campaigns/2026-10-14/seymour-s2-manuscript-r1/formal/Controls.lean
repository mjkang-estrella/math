/- Copyright 2026 Myeongjin Kang. MIT.
Concrete counterexamples to weakening hypotheses, not counterexamples to S2. -/
import SeymourSupport

open scoped BigOperators
namespace SeymourControls

/-- The general threshold m=n²+1 gives zero, not strict negativity. -/
theorem threshold_equality (n : ℤ) :
    n^2 * (n^2 + 1) - (n^2 + 1) * ((n^2 + 1) - 1) = 0 := by ring

/-- An actual ten-fiber family saturates the bad threshold n=2,m=5,
with the required four special fibers and sum zero. -/
theorem threshold_family :
    (Finset.range 4 ⊆ Finset.range 10) ∧
    (∀ i ∈ Finset.range 10 \ Finset.range 4,
      (if i < 4 then (-3 : ℤ) else 2) ≤ 2) ∧
    (∀ i ∈ Finset.range 4, (if i < 4 then (-3 : ℤ) else 2) ≤ 2-5) ∧
    (∑ i ∈ Finset.range 10, (if i < 4 then (-3 : ℤ) else 2)) = 0 := by
  constructor
  · exact Finset.range_mono (by omega)
  constructor
  · intro i hi
    split_ifs <;> omega
  constructor
  · intro i hi
    have : i < 4 := Finset.mem_range.mp hi
    simp [this]
  · norm_num [Finset.sum_range_succ]

/-- With n=2,m=6, having only m−2 anchors again permits total zero. -/
theorem missing_anchor_family :
    (Finset.range 4 ⊆ Finset.range 12) ∧
    (∀ i ∈ Finset.range 12 \ Finset.range 4,
      (if i < 4 then (-4 : ℤ) else 2) ≤ 2) ∧
    (∀ i ∈ Finset.range 4, (if i < 4 then (-4 : ℤ) else 2) ≤ 2-6) ∧
    (∑ i ∈ Finset.range 12, (if i < 4 then (-4 : ℤ) else 2)) = 0 := by
  constructor
  · exact Finset.range_mono (by omega)
  constructor
  · intro i hi
    split_ifs <;> omega
  constructor
  · intro i hi
    have : i < 4 := Finset.mem_range.mp hi
    simp [this]
  · norm_num [Finset.sum_range_succ]

/-- The actual chosen five anchors at n=2,m=6 achieve exactly −m. -/
theorem sharp_negative_family :
    (∑ i ∈ Finset.range 12, (if i < 5 then (-4 : ℤ) else 2)) = -6 := by
  norm_num [Finset.sum_range_succ]

/-- A weak boundary deficit can be zero when the avoiding hypothesis is absent. -/
theorem weak_boundary_not_strict :
    (-1 : ℤ) = 0 + 0 + 0 - 1 ∧
    (0 : ℤ) ≤ 0 ∧ ¬((0 : ℤ) ≤ -1) := by norm_num

/-- Complement gain really needs disjoint old images: both images can be U,
with empty second images and strict individual inequalities, yet no gain.
All four old sets can have size 3 inside a three-point U. -/
theorem disjointness_needed :
    (3 + 0 < 2 * (3 : ℕ)) ∧ (3 + 0 < 2 * (3 : ℕ)) ∧
    ¬(3 + 3 + 2 * 0 < (3 : ℕ) + 3) := by norm_num

/-- Non-strict input gain and the same deletion budget permit equality of
old and new objectives; the strict inequality in pruning is indispensable. -/
theorem strict_gain_needed :
    (6 + 2 * (2 : ℕ) = 5 + 5) ∧ (1 + (1 : ℕ) ≤ 2 + 0) ∧
    (4 + 4 + (0 : ℕ) = 6 + 2) := by norm_num

end SeymourControls
