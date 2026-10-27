import Mathlib

set_option autoImplicit false
set_option warningAsError true

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace CStarCorona

abbrev A := Matrix (Fin 2) (Fin 2) ℂ

def coeff : A := Matrix.diagonal ![(1 / 4 : ℂ), 0]

def nilpotent : A := !![1, 1; -1, -1]

def witness (z : A) : A := 1 + coeff * z

theorem nilpotent_sq : nilpotent ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotent, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem coeff_nilpotent_sq_ne : (coeff * nilpotent) ^ 2 ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : A => M 0 0) h
  norm_num [coeff, nilpotent, pow_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply] at h00

theorem no_affine_nilpotent_right_inverse (t : ℂ) (ht : t ≠ 0) (b : A)
    (hplus : witness (t • nilpotent) * (1 + t • (b * nilpotent)) = 1)
    (hminus : witness ((-t) • nilpotent) * (1 + (-t) • (b * nilpotent)) = 1) :
    False := by
  have hp := congrArg (fun M : A => M 0 0) hplus
  have hm := congrArg (fun M : A => M 0 0) hminus
  have hb := congrArg (fun M : A => M 1 0) hplus
  norm_num [witness, coeff, nilpotent, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply] at hp hm hb
  have hb0 : b 1 0 - b 1 1 = 0 := by
    rcases hb with h | h
    · exact (ht h).elim
    · simpa only [sub_eq_add_neg] using h
  have hs : t ^ 2 * (b 0 0 - b 0 1) = 0 := by
    linear_combination 2 * hp + 2 * hm - t ^ 2 * hb0
  have hb1 : b 0 0 - b 0 1 = 0 :=
    (mul_eq_zero.mp hs).resolve_left (pow_ne_zero 2 ht)
  apply ht
  linear_combination 4 * hp - (4 * t + t ^ 2) * hb1 - t ^ 2 * hb0

end CStarCorona
