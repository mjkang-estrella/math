import PathBorder
import ReducedIdentification

namespace KadarYu

open Matrix Polynomial

theorem jacobiMatrix_prefix (n : ℕ) (diag off : ℕ → ℝ) :
    (jacobiMatrix (n + 1) diag off).submatrix Fin.castSucc Fin.castSucc =
      jacobiMatrix n diag off := by
  apply Matrix.ext
  intro i j
  simp [Matrix.submatrix_apply, jacobiMatrix]

theorem jacobiMatrix_succ_border (n : ℕ) (diag off : ℕ → ℝ) :
    jacobiMatrix (n + 2) diag off =
      pathBorder (jacobiMatrix (n + 1) diag off) (diag (n + 1)) (off n) := by
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) j) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [jacobiMatrix]
    · have hne : Fin.last (n + 1) ≠ j.castSucc := by
        intro h
        have he := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_castSucc] at he
        omega
      have hfar : n + 1 + 1 ≠ j.val := by omega
      by_cases h : j.val = n
      · simp [jacobiMatrix, hne, h]
        omega
      · simp [jacobiMatrix, hne, hfar, h]
  · have hne : i.castSucc ≠ Fin.last (n + 1) := by
      intro h
      have he := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at he
      omega
    have hfar : n + 1 + 1 ≠ i.val := by omega
    by_cases h : i.val = n
    · simp [jacobiMatrix, hne, h]
    · simp [jacobiMatrix, hne, hfar, h]
  · by_cases h : i = j
    · subst j
      simp [jacobiMatrix]
    · simp [jacobiMatrix, h]

noncomputable def jacobiPolynomial (diag off : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  (jacobiMatrix n diag off).charpoly

theorem jacobiPolynomial_zero (diag off : ℕ → ℝ) :
    jacobiPolynomial diag off 0 = 1 := by
  simp [jacobiPolynomial]

theorem jacobiPolynomial_recurrence (diag off : ℕ → ℝ) (n : ℕ) :
    jacobiPolynomial diag off (n + 2) =
      (X - C (diag (n + 1))) * jacobiPolynomial diag off (n + 1) -
        C (off n ^ 2) * jacobiPolynomial diag off n := by
  unfold jacobiPolynomial
  rw [jacobiMatrix_succ_border, pathBorder_charpoly, jacobiMatrix_prefix]

theorem jacobiPolynomial_consecutive_coprime
    (diag off : ℕ → ℝ) (hoff : ∀ n, off n ≠ 0) :
    ∀ n, IsCoprime (jacobiPolynomial diag off n) (jacobiPolynomial diag off (n + 1)) := by
  intro n
  induction n with
  | zero => rw [jacobiPolynomial_zero]; exact isCoprime_one_left
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 from by omega, jacobiPolynomial_recurrence]
    exact coprime_recurrence_step (pow_ne_zero 2 (hoff n)) ih

theorem jacobiPolynomial_squarefree (diag off : ℕ → ℝ) (hoff : ∀ n, off n ≠ 0)
    (n : ℕ) : Squarefree (jacobiPolynomial diag off n) :=
  jacobiMatrix_charpoly_squarefree n diag off (fun i _ => hoff i)

end KadarYu
