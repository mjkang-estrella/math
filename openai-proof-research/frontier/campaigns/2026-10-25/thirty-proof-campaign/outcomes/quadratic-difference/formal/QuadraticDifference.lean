import Mathlib

open Matrix Polynomial
namespace QuadraticDifferenceCounterexample
noncomputable section

abbrev V := Fin 2 → ℝ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

def J : Mat := !![0, 1; -1, 0]
def b : LinearMap.BilinForm ℝ V := Matrix.toBilin' J

def p : Polynomial ℝ := X ^ 2 + 1

def BAlternating (M : Mat) : Prop := ∀ x : V, b x (M *ᵥ x) = 0

def Difference (u : Mat) : Prop :=
  ∃ M N : Mat, aeval M p = 0 ∧ aeval N p = 0 ∧ u = M - N

def SymplecticDifference (u : Mat) : Prop :=
  ∃ M N : Mat, BAlternating M ∧ BAlternating N ∧
    aeval M p = 0 ∧ aeval N p = 0 ∧ u = M - N

theorem form_eval (x y : V) : b x y = x 0 * y 1 - x 1 * y 0 := by
  simp [b, J, Matrix.toBilin'_apply', dotProduct, mulVec, Fin.sum_univ_two]
  ring

theorem form_alternating : b.IsAlt := by
  intro x
  rw [form_eval]
  ring

theorem form_nondegenerate : b.Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' J
  norm_num [J, Matrix.det_fin_two]

theorem p_monic : p.Monic := by
  apply Polynomial.Monic.add_of_left (Polynomial.monic_X_pow 2)
  norm_num

theorem p_degree : p.natDegree = 2 := by
  norm_num [p]

theorem polynomial_eval (M : Mat) : aeval M p = M ^ 2 + 1 := by
  simp [p]

theorem rotation_root : aeval J p = 0 := by
  rw [polynomial_eval]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J, pow_two, Matrix.mul_fin_two]

theorem zero_difference : Difference (0 : Mat) := by
  exact ⟨J, J, rotation_root, rotation_root, by simp⟩

theorem zero_alternating : BAlternating (0 : Mat) := by
  intro x
  simp [form_eval]

theorem alternating_scalar (M : Mat) (h : BAlternating M) :
    M = (M 0 0) • (1 : Mat) := by
  have h0 := h ![1, 0]
  have h1 := h ![0, 1]
  have h2 := h ![1, 1]
  simp [form_eval] at h0 h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1]
  linarith

theorem no_alternating_root (M : Mat) (h : BAlternating M) : aeval M p ≠ 0 := by
  intro hz
  rw [polynomial_eval, alternating_scalar M h] at hz
  have he := congrArg (fun a : Mat => a 0 0) hz
  norm_num [pow_two, Matrix.mul_fin_two] at he
  nlinarith [sq_nonneg (M 0 0)]

theorem zero_not_symplectic_difference : ¬ SymplecticDifference (0 : Mat) := by
  rintro ⟨M, _, hM, _, hpM, _⟩
  exact no_alternating_root M hM hpM

theorem source_counterexample :
    b.IsAlt ∧ b.Nondegenerate ∧ p.Monic ∧ p.natDegree = 2 ∧
    BAlternating (0 : Mat) ∧ Difference (0 : Mat) ∧
    ¬ SymplecticDifference (0 : Mat) := by
  exact ⟨form_alternating, form_nondegenerate, p_monic, p_degree,
    zero_alternating, zero_difference, zero_not_symplectic_difference⟩

def EndBAlternating (f : Module.End ℝ V) : Prop := ∀ x : V, b x (f x) = 0

def EndDifference (u : Module.End ℝ V) : Prop :=
  ∃ f g : Module.End ℝ V, aeval f p = 0 ∧ aeval g p = 0 ∧ u = f - g

def EndSymplecticDifference (u : Module.End ℝ V) : Prop :=
  ∃ f g : Module.End ℝ V, EndBAlternating f ∧ EndBAlternating g ∧
    aeval f p = 0 ∧ aeval g p = 0 ∧ u = f - g

theorem root_end_iff (M : Mat) :
    aeval (Matrix.toLinAlgEquiv' M) p = 0 ↔ aeval M p = 0 := by
  have h : aeval (Matrix.toLinAlgEquiv' M) p = Matrix.toLinAlgEquiv' (aeval M p) := by
    simp [p]
  rw [h]
  exact map_eq_zero_iff Matrix.toLinAlgEquiv' Matrix.toLinAlgEquiv'.injective

theorem source_endomorphism_counterexample :
    b.IsAlt ∧ b.Nondegenerate ∧ p.Monic ∧ p.natDegree = 2 ∧
    EndBAlternating (0 : Module.End ℝ V) ∧ EndDifference (0 : Module.End ℝ V) ∧
    ¬ EndSymplecticDifference (0 : Module.End ℝ V) := by
  refine ⟨form_alternating, form_nondegenerate, p_monic, p_degree, ?_, ?_, ?_⟩
  · intro x
    simp
  · exact ⟨Matrix.toLinAlgEquiv' J, Matrix.toLinAlgEquiv' J,
      (root_end_iff J).mpr rotation_root, (root_end_iff J).mpr rotation_root, by simp⟩
  · rintro ⟨f, _, hf, _, hroot, _⟩
    obtain ⟨M, rfl⟩ := Matrix.toLinAlgEquiv'.surjective f
    have hM : BAlternating M := by
      intro x
      exact hf x
    exact no_alternating_root M hM ((root_end_iff M).mp hroot)

end
end QuadraticDifferenceCounterexample
