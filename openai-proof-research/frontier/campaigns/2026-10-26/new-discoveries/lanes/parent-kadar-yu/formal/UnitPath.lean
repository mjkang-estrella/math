import JacobiDeterminants

namespace KadarYu

open Polynomial

theorem unitPath_polynomial_eq_S (n : ℕ) :
    jacobiPolynomial (fun _ => 0) (fun _ => 1) n = Polynomial.Chebyshev.S ℝ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [jacobiPolynomial_zero]
  | one =>
    have hm : jacobiMatrix 1 (fun _ => 0) (fun _ => 1) = 0 := by
      ext i j
      fin_cases i
      fin_cases j
      simp [jacobiMatrix]
    simp [jacobiPolynomial, hm]
  | more n ih0 ih1 =>
    rw [jacobiPolynomial_recurrence, ih0, ih1]
    push_cast
    simp

theorem unitPath_root_param {n : ℕ} {x : ℝ}
    (hx : (jacobiPolynomial (fun _ => 0) (fun _ => 1) n).eval x = 0) :
    ∃ k : ℕ, k < n ∧ x = 2 * Real.cos ((k + 1) * Real.pi / (n + 1)) := by
  rw [unitPath_polynomial_eq_S] at hx
  have hU : (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (x / 2) = 0 := by
    rw [← Polynomial.Chebyshev.S_comp_two_mul_X]
    simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, mul_div_cancel₀ x (by norm_num : (2 : ℝ) ≠ 0)] using hx
  have hn : (n : ℤ) ≠ -1 := by omega
  have hmem := (Polynomial.mem_roots (Polynomial.Chebyshev.U_ne_zero ℝ _ hn)).mpr hU
  rw [Polynomial.Chebyshev.roots_U_real] at hmem
  rw [Finset.mem_val] at hmem
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hmem
  refine ⟨k, Finset.mem_range.mp hk, ?_⟩
  linarith

theorem unitPath_root_in_band {n : ℕ} {x : ℝ}
    (hx : (jacobiPolynomial (fun _ => 0) (fun _ => 1) n).eval x = 0) :
    x ∈ Set.Ioo (-2 : ℝ) 2 := by
  obtain ⟨k, hk, rfl⟩ := unitPath_root_param hx
  have hd : (0 : ℝ) < n + 1 := by positivity
  have htheta : 0 < (k + 1 : ℝ) * Real.pi / (n + 1) := by positivity
  have hlt : (k + 1 : ℝ) * Real.pi / (n + 1) < Real.pi := by
    apply (div_lt_iff₀ hd).mpr
    have hh : (k + 1 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_lt_succ hk
    nlinarith [Real.pi_pos]
  have hu := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
    hlt.le htheta
  have hl := Real.cos_lt_cos_of_nonneg_of_le_pi htheta.le (le_refl Real.pi) hlt
  simp only [Real.cos_zero] at hu
  simp only [Real.cos_pi] at hl
  constructor <;> nlinarith

theorem unitPath_eigenvalues_in_band (n : ℕ) (i : Fin n) :
    (jacobiMatrix_hermitian n (fun _ => 0) (fun _ => 1)).eigenvalues i ∈
      Set.Ioo (-2 : ℝ) 2 := by
  let A := jacobiMatrix n (fun _ => 0) (fun _ => 1)
  let hA := jacobiMatrix_hermitian n (fun _ => 0) (fun _ => 1)
  have hm : hA.eigenvalues i ∈ A.charpoly.roots := by
    rw [hA.roots_charpoly_eq_eigenvalues]
    apply Multiset.mem_map.mpr
    exact ⟨i, by simp, by simp⟩
  have hz := (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mp hm
  exact unitPath_root_in_band hz

end KadarYu
