import UnboundedGap

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarSmaleUnbounded

open Polynomial

theorem cubicPolynomial_monic {A : Type*} [CommRing A] (a : Fin 3 → A) :
    (cubicPolynomial a).Monic :=
  ((monic_X_sub_C _).mul (monic_X_sub_C _)).mul (monic_X_sub_C _)

theorem cubicPolynomial_degree {A : Type*} [CommRing A] [Nontrivial A] (a : Fin 3 → A) :
    (cubicPolynomial a).natDegree = 3 := by
  unfold cubicPolynomial
  rw [((monic_X_sub_C _).mul (monic_X_sub_C _)).natDegree_mul (monic_X_sub_C _),
    (monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
  simp

theorem both_critical_branches (epsilon : ℝ) :
    cubicDeleted (roots epsilon) (branch epsilon) = 0 ∧
      cubicDeleted (roots epsilon) (-branch epsilon) = 0 := by
  constructor <;> rw [deleted_eq] <;> ring

theorem critical_iff (epsilon : ℝ) (he : 0 < epsilon) (w : FunctionAlgebra) :
    cubicDeleted (roots epsilon) w = 0 ↔ w = branch epsilon ∨ w = -branch epsilon := by
  constructor
  · exact critical_complete epsilon he w
  · rintro (rfl | rfl)
    · exact (both_critical_branches epsilon).1
    · exact (both_critical_branches epsilon).2

theorem branch_distinct (epsilon : ℝ) (he : 0 < epsilon) :
    branch epsilon ≠ -branch epsilon := by
  intro h
  exact branch_apart epsilon he timeZero (congrArg (fun f : FunctionAlgebra => f timeZero) h)

theorem deleted_coordinate_unit (epsilon : ℝ) (he : 0 < epsilon) :
    IsUnit (cubicDeleted (roots epsilon) coordinate) := by
  rw [deleted_coordinate epsilon he.le]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨ContinuousMap.const Time ((-3 * (epsilon : ℂ))⁻¹), ?_⟩
  ext t
  change (-3 * (epsilon : ℂ)) * (-3 * (epsilon : ℂ))⁻¹ = 1
  exact mul_inv_cancel₀ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr he.ne'))

def chosenParameter (C : ℝ) : ℝ := 1 / (16 * (C + 1))

theorem chosenParameter_pos (C : ℝ) (hC : 0 ≤ C) : 0 < chosenParameter C := by
  unfold chosenParameter
  positivity

theorem chosenParameter_le (C : ℝ) (hC : 0 ≤ C) : chosenParameter C ≤ 1 / 16 := by
  unfold chosenParameter
  apply (div_le_iff₀ (by positivity : 0 < 16 * (C + 1))).mpr
  nlinarith

theorem chosenParameter_weighted (C : ℝ) (hC : 0 ≤ C) : C * chosenParameter C ≤ 1 / 16 := by
  unfold chosenParameter
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < 16 * (C + 1))).mpr
  nlinarith

theorem every_critical_exceeds (C : ℝ) (hC : 0 ≤ C) (w : FunctionAlgebra)
    (hw : cubicDeleted (roots (chosenParameter C)) w = 0) :
    C * ‖cubicDeleted (roots (chosenParameter C)) coordinate‖ <
      ‖cubicValue (roots (chosenParameter C)) coordinate -
        cubicValue (roots (chosenParameter C)) w‖ / ‖coordinate - w‖ := by
  have he0 := chosenParameter_pos C hC
  have he1 := chosenParameter_le C hC
  have hpos := critical_distance_pos (chosenParameter C) he0 w hw
  have hdist := critical_distance_le (chosenParameter C) he0 he1 w hw
  have hgap := critical_value_gap (chosenParameter C) he0 w hw
  apply (lt_div_iff₀ hpos).mpr
  rw [deleted_coordinate_norm (chosenParameter C) he0]
  have hb := mul_le_mul_of_nonneg_left hdist
    (mul_nonneg hC (by positivity : 0 ≤ 3 * chosenParameter C))
  have hc := chosenParameter_weighted C hC
  nlinarith

def InfiniteConstantTheorem : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ (a : Fin 3 → FunctionAlgebra) (z bp bm : FunctionAlgebra),
    (cubicPolynomial a).Monic ∧ (cubicPolynomial a).natDegree = 3 ∧
    IsUnit (cubicDeleted a z) ∧ bp ≠ bm ∧
    (∀ w : FunctionAlgebra, cubicDeleted a w = 0 ↔ w = bp ∨ w = bm) ∧
    ∀ w : FunctionAlgebra, cubicDeleted a w = 0 →
      C * ‖cubicDeleted a z‖ < ‖cubicValue a z - cubicValue a w‖ / ‖z - w‖

theorem infinite_cubic_constant : InfiniteConstantTheorem := by
  intro C hC
  let e := chosenParameter C
  have he : 0 < e := chosenParameter_pos C hC
  refine ⟨roots e, coordinate, branch e, -branch e, cubicPolynomial_monic _,
    cubicPolynomial_degree _, deleted_coordinate_unit e he, branch_distinct e he,
    critical_iff e he, ?_⟩
  intro w hw
  exact every_critical_exceeds C hC w hw

def CubicBound (C : ℝ) : Prop :=
  ∀ (a : Fin 3 → FunctionAlgebra) (z : FunctionAlgebra), cubicDeleted a z ≠ 0 →
    ∃ w : FunctionAlgebra, cubicDeleted a w = 0 ∧
      ‖cubicValue a z - cubicValue a w‖ / ‖z - w‖ ≤ C * ‖cubicDeleted a z‖

theorem no_finite_cubic_bound : ¬∃ C : ℝ, 0 ≤ C ∧ CubicBound C := by
  rintro ⟨C, hC, hb⟩
  obtain ⟨w, hw, hc⟩ := hb (roots (chosenParameter C)) coordinate
    (deleted_coordinate_ne _ (chosenParameter_pos C hC))
  exact (not_lt_of_ge hc) (every_critical_exceeds C hC w hw)

end CStarSmaleUnbounded
