import CosineBridge

open scoped Matrix.Norms.Operator
open Matrix
namespace Novak
noncomputable def plane (a b : ℝ) : M₂ := !![(a : ℂ), (b : ℂ); (b : ℂ), -(a : ℂ)]

lemma plane_square (a b : ℝ) :
    plane a b * plane a b = scalar ((a : ℂ)^2+(b : ℂ)^2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plane, Matrix.mul_apply, Fin.sum_univ_two, scalar] <;> ring

lemma cos_plane (a b r : ℝ) (hr : r ≠ 0) (h : a^2+b^2=r^2) :
    operatorCos (plane a b) = scalar (Real.cos r) := by
  apply cos_square _ r hr
  rw [plane_square]
  congr 1
  exact_mod_cast h

noncomputable def U : M₂ := plane (2*Real.pi) 0
noncomputable def V : M₂ := plane (-7*Real.pi/4) (Real.pi*Real.sqrt 15/4)

lemma plane_add (a b c d : ℝ) : plane a b + plane c d = plane (a+c) (b+d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane, add_comm]

lemma plane_sub (a b c d : ℝ) : plane a b - plane c d = plane (a-c) (b-d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane, sub_eq_add_neg, add_comm]

lemma plane_selfAdjoint (a b : ℝ) : (plane a b).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane, Matrix.conjTranspose_apply]

lemma cos_U : operatorCos U = 1 := by
  rw [U, cos_plane _ _ (2*Real.pi) (by positivity) (by ring)]
  simp [Real.cos_two_pi, scalar]

lemma cos_V : operatorCos V = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)
  have hv : (-7*Real.pi/4)^2+(Real.pi*Real.sqrt 15/4)^2=(2*Real.pi)^2 := by
    nlinarith [sq_nonneg Real.pi]
  rw [V, cos_plane _ _ (2*Real.pi) (by positivity) hv]
  simp [Real.cos_two_pi, scalar]

lemma cos_sum : operatorCos (U+V) = -1 := by
  rw [U, V, plane_add]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)
  have hv : (2*Real.pi+-7*Real.pi/4)^2+(0+Real.pi*Real.sqrt 15/4)^2=Real.pi^2 := by
    nlinarith [sq_nonneg Real.pi]
  rw [cos_plane _ _ Real.pi (ne_of_gt Real.pi_pos) hv]
  simp [Real.cos_pi, scalar]

lemma cos_difference : operatorCos (U-V) = scalar (Real.cos (Real.pi*Real.sqrt 15)) := by
  rw [U, V, plane_sub]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)
  apply cos_plane _ _ _ (by positivity)
  nlinarith [sq_nonneg Real.pi]

lemma cos_neg (A : M₂) : operatorCos (-A) = operatorCos A := by
  simp only [operatorCos, smul_neg, neg_neg, add_comm]

lemma cos_zero : operatorCos 0 = 1 := by
  unfold operatorCos
  rw [smul_zero, neg_zero, NormedSpace.exp_zero]
  have h : (1:M₂) + 1 = (2:ℂ) • (1:M₂) := by module
  rw [h, smul_smul]
  norm_num
end Novak
