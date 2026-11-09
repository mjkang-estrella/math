import Mathlib

/-! Exact rational specialization (s = 1) of Shivam Patel's posted family.
The target is Conjecture 1.1 of Banerjee--Chaudhury, arXiv:2509.06715v1.
All spectral radii below are mathlib's ENNReal-valued spectralRadius over ℂ.
-/
namespace SchurStability

noncomputable section

open Matrix
open scoped ENNReal NNReal

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ
abbrev CMat := Matrix (Fin 2) (Fin 2) ℂ

def W : Mat := !![0, 1; 1/4, 3/4]
def B : Mat := !![9/11, -4/11; -4/11, 3/11]
def e : Fin 2 → ℝ := ![1, 1]
def pi : Fin 2 → ℝ := ![1/5, 4/5]
def t : ℝ := 1

def P (A D : Mat) (s : ℝ) : Mat := A * (1 - s • D)
noncomputable def R (A D : Mat) (s : ℝ) : Mat :=
  1 - A + (1 + s • D)⁻¹ * (2 • A - 1)
noncomputable def complexify (A : Mat) : CMat := A.map (algebraMap ℝ ℂ)
noncomputable def rho (A : Mat) : ℝ≥0∞ := spectralRadius ℂ (complexify A)
noncomputable def realRho (A : Mat) : ℝ := (rho A).toReal

def RowStochastic (A : Mat) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ ∀ i, ∑ j, A i j = 1

def Primitive (A : Mat) : Prop := ∃ k : ℕ, 0 < k ∧ ∀ i j, 0 < (A ^ k) i j

noncomputable def SchurStable (A : Mat) : Prop := rho A < 1

theorem W_stochastic : RowStochastic W := by
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [W]
  · intro i; fin_cases i <;> norm_num [W, Fin.sum_univ_two]

theorem W_square : W ^ 2 = !![1/4, 3/4; 3/16, 13/16] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, W, Matrix.mul_apply, Fin.sum_univ_two]

theorem W_primitive : Primitive W := by
  refine ⟨2, by norm_num, ?_⟩
  intro i j; rw [W_square]
  fin_cases i <;> fin_cases j <;> norm_num

theorem pi_positive : ∀ i, 0 < pi i := by
  intro i; fin_cases i <;> norm_num [pi]

theorem pi_normalized : ∑ i, pi i = 1 := by norm_num [pi, Fin.sum_univ_two]

theorem pi_stationary : pi ᵥ* W = pi := by
  ext i; fin_cases i <;> norm_num [pi, W, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem W_fixes_e : W *ᵥ e = e := by
  ext i; fin_cases i <;> norm_num [W, e, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem B_hermitian : B.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [B, Matrix.conjTranspose_apply]

theorem B_quadratic (x : Fin 2 → ℝ) :
    11 * (x ⬝ᵥ (B *ᵥ x)) =
      8 * (x 0 - x 1 / 2)^2 + (x 0)^2 + (x 1)^2 := by
  simp [B, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem B_posDef : B.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos B_hermitian
  intro x hx
  have hsq : 0 < (x 0)^2 + (x 1)^2 := by
    by_contra h
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    apply hx
    ext i; fin_cases i <;> simp [h0, h1]
  have hid := B_quadratic x
  have hn := sq_nonneg (x 0 - x 1 / 2)
  simp only [star_trivial] at *
  nlinarith

theorem B_posSemidef : B.PosSemidef := B_posDef.posSemidef

theorem B_e : B *ᵥ e = ![5/11, -1/11] := by
  ext i; fin_cases i <;> norm_num [B, e, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem B_e_le_e : ∀ i, (B *ᵥ e) i ≤ e i := by
  intro i; rw [B_e]; fin_cases i <;> norm_num [e]

theorem pi_B_e : pi ⬝ᵥ (B *ᵥ e) = 1/55 := by
  rw [B_e]; norm_num [pi, dotProduct, Fin.sum_univ_two]

theorem pi_B_e_positive : 0 < pi ⬝ᵥ (B *ᵥ e) := by rw [pi_B_e]; norm_num

def J : Mat := !![7/12, 1/6; 1/6, 5/6]

theorem inverse_left : J * (1 + t • B) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, B, t, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem inverse_right : (1 + t • B) * J = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, B, t, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem actual_inverse : (1 + t • B)⁻¹ = J := Matrix.inv_eq_left_inv inverse_left

theorem P_exact : P W B t = !![4/11, 8/11; 7/22, 7/11] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [P, W, B, t, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem R_exact : R W B t = !![1/2, 1/4; 0, 1] := by
  unfold R
  rw [actual_inverse]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [J, W, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply]

theorem B_eigen_one : B *ᵥ ![2, -1] = ![2, -1] := by
  ext i; fin_cases i <;> norm_num [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem B_eigen_small : B *ᵥ ![1, 2] = (1/11 : ℝ) • ![1, 2] := by
  ext i; fin_cases i <;> norm_num [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem P_eigen_one : P W B t *ᵥ ![8, 7] = ![8, 7] := by
  rw [P_exact]
  ext i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem R_eigen_one : R W B t *ᵥ ![1, 2] = ![1, 2] := by
  rw [R_exact]
  ext i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Spectrum membership is actual noninvertibility in the complex matrix algebra. -/
theorem spectrum_iff_det_zero (A : CMat) (z : ℂ) :
    z ∈ spectrum ℂ A ↔ (algebraMap ℂ CMat z - A).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  simp only [isUnit_iff_ne_zero, not_not]

theorem B_char_det (z : ℂ) :
    (algebraMap ℂ CMat z - complexify B).det = (z - 1) * (z - 1/11) := by
  simp [Matrix.det_fin_two, Matrix.algebraMap_eq_diagonal, complexify, B]
  ring

theorem W_char_det (z : ℂ) :
    (algebraMap ℂ CMat z - complexify W).det = (z - 1) * (z + 1/4) := by
  simp [Matrix.det_fin_two, Matrix.algebraMap_eq_diagonal, complexify, W]
  ring

theorem P_char_det (z : ℂ) :
    (algebraMap ℂ CMat z - complexify (P W B t)).det = (z - 1) * z := by
  rw [P_exact]
  simp [Matrix.det_fin_two, Matrix.algebraMap_eq_diagonal, complexify]
  ring

theorem R_char_det (z : ℂ) :
    (algebraMap ℂ CMat z - complexify (R W B t)).det = (z - 1) * (z - 1/2) := by
  rw [R_exact]
  simp [Matrix.det_fin_two, Matrix.algebraMap_eq_diagonal, complexify]
  ring

theorem B_spectrum (z : ℂ) : z ∈ spectrum ℂ (complexify B) ↔ z = 1 ∨ z = 1/11 := by
  rw [spectrum_iff_det_zero, B_char_det, mul_eq_zero]
  simp only [sub_eq_zero]

theorem W_spectrum (z : ℂ) : z ∈ spectrum ℂ (complexify W) ↔ z = 1 ∨ z = -1/4 := by
  rw [spectrum_iff_det_zero, W_char_det, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (sub_eq_zero.mp h)
    · right; linear_combination h
  · rintro (h | h) <;> norm_num [h]

theorem P_spectrum (z : ℂ) : z ∈ spectrum ℂ (complexify (P W B t)) ↔ z = 1 ∨ z = 0 := by
  rw [spectrum_iff_det_zero, P_char_det, mul_eq_zero]
  simp only [sub_eq_zero]

theorem R_spectrum (z : ℂ) : z ∈ spectrum ℂ (complexify (R W B t)) ↔ z = 1 ∨ z = 1/2 := by
  rw [spectrum_iff_det_zero, R_char_det, mul_eq_zero]
  simp only [sub_eq_zero]

/-- Finite-dimensional eigenvalues agree with the matrix algebra spectrum. -/
theorem eigenvalue_iff_spectrum (A : CMat) (z : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' A) z ↔ z ∈ spectrum ℂ A := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, AlgEquiv.spectrum_eq]

theorem P_complex_eigenvector :
    Module.End.HasEigenvector (Matrix.toLinAlgEquiv' (complexify (P W B t))) 1 ![8, 7] := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · rw [Matrix.toLinAlgEquiv'_apply, P_exact]
    ext i; fin_cases i <;>
      norm_num [complexify, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    have h0 := congrFun h 0
    norm_num at h0

theorem R_complex_eigenvector :
    Module.End.HasEigenvector (Matrix.toLinAlgEquiv' (complexify (R W B t))) 1 ![1, 2] := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · rw [Matrix.toLinAlgEquiv'_apply, R_exact]
    ext i; fin_cases i <;>
      norm_num [complexify, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    have h0 := congrFun h 0
    norm_num at h0

theorem P_hasEigenvalue :
    Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' (complexify (P W B t))) 1 :=
  Module.End.hasEigenvalue_of_hasEigenvector P_complex_eigenvector

theorem R_hasEigenvalue :
    Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' (complexify (R W B t))) 1 :=
  Module.End.hasEigenvalue_of_hasEigenvector R_complex_eigenvector

/-- A finite spectrum with the displayed two elements has radius exactly one. -/
theorem radius_eq_one (A : CMat) (c : ℂ)
    (hs : ∀ z, z ∈ spectrum ℂ A ↔ z = 1 ∨ z = c) (hc : ‖c‖₊ ≤ 1) :
    spectralRadius ℂ A = 1 := by
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm
  · apply iSup₂_le
    intro z hz
    rcases (hs z).mp hz with rfl | rfl
    · simp
    · exact_mod_cast hc
  · have hm : (1 : ℂ) ∈ spectrum ℂ A := (hs 1).mpr (Or.inl rfl)
    exact le_iSup₂_of_le (1 : ℂ) hm (by simp)

theorem rho_B : rho B = 1 := by
  apply radius_eq_one _ (1/11) B_spectrum
  norm_num [nnnorm_div, div_le_one]

theorem rho_W : rho W = 1 := by
  apply radius_eq_one _ (-1/4) W_spectrum
  norm_num [nnnorm_div, div_le_one]

theorem rho_P : rho (P W B t) = 1 := by
  apply radius_eq_one _ 0 P_spectrum
  simp

theorem rho_R : rho (R W B t) = 1 := by
  apply radius_eq_one _ (1/2) R_spectrum
  norm_num [nnnorm_div, div_le_one]

theorem realRho_B : realRho B = 1 := by simp [realRho, rho_B]

theorem B_source_bound : ∀ i, (B *ᵥ e) i ≤ realRho B * e i := by
  simpa only [realRho_B, one_mul] using B_e_le_e

theorem strict_step : 0 < t ∧ t < 2 / realRho B := by rw [realRho_B]; norm_num [t]

theorem pi_is_left_Perron : pi ᵥ* W = realRho W • pi := by
  simpa [realRho, rho_W] using pi_stationary

theorem P_not_stable : ¬ SchurStable (P W B t) := by simp [SchurStable, rho_P]
theorem R_not_stable : ¬ SchurStable (R W B t) := by simp [SchurStable, rho_R]

theorem realRho_P : realRho (P W B t) = 1 := by simp [realRho, rho_P]
theorem realRho_R : realRho (R W B t) = 1 := by simp [realRho, rho_R]

theorem P_not_real_stable : ¬ realRho (P W B t) < 1 := by rw [realRho_P]; exact lt_irrefl 1
theorem R_not_real_stable : ¬ realRho (R W B t) < 1 := by rw [realRho_R]; exact lt_irrefl 1

/-- The normalized form of exactly the source's hypotheses, specialized to dimension two. -/
def SourceHypotheses (A D : Mat) (v : Fin 2 → ℝ) : Prop :=
  RowStochastic A ∧ Primitive A ∧ D.PosSemidef ∧
  (∀ i, 0 < v i) ∧ (∑ i, v i = 1) ∧
  v ᵥ* A = realRho A • v ∧
  (∀ i, (D *ᵥ e) i ≤ realRho D * e i) ∧
  0 < v ⬝ᵥ (D *ᵥ e)

theorem source_hypotheses : SourceHypotheses W B pi :=
  ⟨W_stochastic, W_primitive, B_posSemidef, pi_positive, pi_normalized,
    pi_is_left_Perron, B_source_bound, pi_B_e_positive⟩

/-- The P assertion of Conjecture 1.1 already restricted to dimension two. -/
def ConjectureP : Prop := ∀ (A D : Mat) (v : Fin 2 → ℝ) (s : ℝ),
  SourceHypotheses A D v → 0 < s → s < 2 / realRho D → SchurStable (P A D s)

/-- The R assertion of Conjecture 1.1 already restricted to dimension two. -/
def ConjectureR : Prop := ∀ (A D : Mat) (v : Fin 2 → ℝ) (s : ℝ),
  SourceHypotheses A D v → 0 < s → s < 2 / realRho D → SchurStable (R A D s)

theorem conjecture_P_false : ¬ ConjectureP := by
  intro h
  exact P_not_stable (h W B pi t source_hypotheses strict_step.1 strict_step.2)

theorem conjecture_R_false : ¬ ConjectureR := by
  intro h
  exact R_not_stable (h W B pi t source_hypotheses strict_step.1 strict_step.2)

theorem both_conjectures_false : ¬ ConjectureP ∧ ¬ ConjectureR :=
  ⟨conjecture_P_false, conjecture_R_false⟩

/-- The source hypotheses, the strict allowed step, and failure of both conclusions. -/
theorem schur_counterexample :
    RowStochastic W ∧ Primitive W ∧ B.PosSemidef ∧ B.PosDef ∧
    (∀ i, 0 < pi i) ∧ (∑ i, pi i = 1) ∧
    pi ᵥ* W = realRho W • pi ∧
    (∀ i, (B *ᵥ e) i ≤ realRho B * e i) ∧
    0 < pi ⬝ᵥ (B *ᵥ e) ∧
    0 < t ∧ t < 2 / realRho B ∧
    ¬ SchurStable (P W B t) ∧ ¬ SchurStable (R W B t) := by
  exact ⟨W_stochastic, W_primitive, B_posSemidef, B_posDef, pi_positive,
    pi_normalized, pi_is_left_Perron, B_source_bound, pi_B_e_positive,
    strict_step.1, strict_step.2, P_not_stable, R_not_stable⟩

end

end SchurStability
