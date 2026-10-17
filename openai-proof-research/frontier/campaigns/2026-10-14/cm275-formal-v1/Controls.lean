/- Copyright 2026 Myeongjin Kang. Released under the MIT license. -/
import CM275
open scoped BigOperators
open RCLike
namespace CMControls

-- Duplicate modes really collide: the averaged sample energy is four, not two.
theorem duplicate_energy :
    ⟪CM275.sample (fun _ : Fin 2 => (1 : AddChar (ZMod 1) ℂ)) (fun _ => 1),
      CM275.sample (fun _ : Fin 2 => (1 : AddChar (ZMod 1) ℂ)) (fun _ => 1)⟫ₙ_[ℂ] = 4 := by
  norm_num [CM275.sample, wInner, cWeight, Fin.sum_univ_two, RCLike.inner_apply]

theorem duplicate_coefficients : (∑ _ : Fin 2, (star (1 : ℂ)) * 1) = 2 := by norm_num

theorem centered_alias :
    ((0 : ZMod 2) - 1) = ((2 : ZMod 2) - 1) := by decide

theorem centered_alias_not_injective :
    ¬ Function.Injective (fun i : Fin 3 => (i.val : ZMod 2) - 1) := by
  intro h
  have h' := h (a₁ := (0 : Fin 3)) (a₂ := (2 : Fin 3)) (by decide)
  norm_num at h'

theorem centered_safe :
    Function.Injective (fun i : Fin 3 => (i.val : ZMod 3) - 1) := by
  exact CM275.centered_modes_injective (q := 3) (K := 1) (by norm_num)

theorem nonunit_phase : star (2 : ℂ) * 2 = 4 ∧ star (2 : ℂ) * 2 ≠ 1 := by norm_num

-- The sign-isotypic average of an involution U is (I-U)/2; here U=-I.
theorem sign_involution_test :
    ((1 : ℝ) - (-1)) / 2 = 1 ∧ ((1 : ℝ) + (-1)) / 2 = 0 := by norm_num

-- Constant weight two is not a character: at the identity its average is 2I.
theorem noncharacter_idempotence_fails :
    (2 : ℝ) * (2 * 1) ≠ 2 * 1 := by norm_num

theorem overweight_fails :
    ¬ ((2 : ℝ) * (1 / 4) ≤ 1 / 4) := by norm_num

theorem negative_probability_fails :
    ¬ ((0 : ℝ) * (-1) ≤ -1) := by norm_num

theorem actual_yes_boundary :
    (1 / 2 + (1 : ℝ) / 10) ≤ CM275.acceptance (2 / 100) (1 / 2) 1 := by
  norm_num [CM275.acceptance]

theorem actual_no_boundary :
    CM275.acceptance (1 - 2 / 100) (1 / 2) 1 ≤ (1 / 2 - (1 : ℝ) / 10) := by
  norm_num [CM275.acceptance]

theorem wrong_tight_margin_fails :
    ¬ ((1 / 2 + (1 : ℝ) / 8) ≤ CM275.acceptance (2 / 100) (1 / 2) 1) := by
  norm_num [CM275.acceptance]

theorem approximation_loss_needed :
    (59 / 100 : ℝ) < 1 / 2 + 1 / 10 ∧
    |(59 / 100 : ℝ) - (1 / 2 + 1 / 10)| ≤ (1 / 10) / 10 := by norm_num

end CMControls
