import DensityTransfer

/- Literal finite symmetric head with one appended path. The head need not be
tridiagonal or cyclic. Source Gram matrices alpha*I+G correspond to head -G and
coupling -1 after the attaching coordinate has been placed last. -/
namespace KadarYu

open Matrix Finset

noncomputable def headTailMatrix (h : ℕ) (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ)
    (c : ℝ) (s : ℕ) : Matrix (Fin (h + s + 1)) (Fin (h + s + 1)) ℝ := fun i j =>
  if hij : i.val < h + 1 ∧ j.val < h + 1 then
    A ⟨i.val, hij.1⟩ ⟨j.val, hij.2⟩
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then c else 0

theorem headTailMatrix_zero (h : ℕ) (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ)
    (c : ℝ) : headTailMatrix h A c 0 = A := by
  apply Matrix.ext
  intro i j
  simp [headTailMatrix, i.isLt, j.isLt]

theorem headTailMatrix_hermitian (h : ℕ) {A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ}
    (hA : A.IsHermitian) (c : ℝ) (s : ℕ) : (headTailMatrix h A c s).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hi : i.val < h + 1
  · by_cases hj : j.val < h + 1
    · simpa [headTailMatrix, hi, hj] using hA.apply ⟨i.val, hi⟩ ⟨j.val, hj⟩
    · simp [headTailMatrix, hi, hj, or_comm]
  · simp [headTailMatrix, hi, and_comm, or_comm]

theorem headTailMatrix_prefix (h : ℕ) (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ)
    (c : ℝ) (s : ℕ) :
    (headTailMatrix h A c (s + 1)).submatrix Fin.castSucc Fin.castSucc =
      headTailMatrix h A c s := by
  apply Matrix.ext
  intro i j
  simp [Matrix.submatrix_apply, headTailMatrix]

theorem headTailMatrix_succ_border (h : ℕ) (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ)
    (c : ℝ) (s : ℕ) :
    headTailMatrix h A c (s + 1) = pathBorder (headTailMatrix h A c s) 0 c := by
  refine Matrix.ext fun (i j : Fin ((h + s + 1) + 1)) => ?_
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) j) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [headTailMatrix]
    · rw [pathBorder_last_cast]
      have hn : ¬ h + s + 1 < h + 1 := by omega
      have hf : ¬ h + s + 1 + 1 = j.val := by omega
      simp only [headTailMatrix, Fin.val_last, Fin.val_castSucc, hn, false_and,
        dite_false, hf, false_or]
  · rw [pathBorder_cast_last]
    have hn : ¬ h + s + 1 < h + 1 := by omega
    have hf : ¬ h + s + 1 + 1 = i.val := by omega
    simp only [headTailMatrix, Fin.val_last, Fin.val_castSucc, hn, and_false,
      dite_false, hf, or_false]
  · simp [headTailMatrix]

theorem headTailMatrix_tail_block (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (s : ℕ) :
    ((headTailMatrix h A c s).submatrix
      (fun i : Fin (h + 1) ⊕ Fin s =>
        Fin.cast (by omega : h + 1 + s = h + s + 1) (finSumFinEquiv i))
      (fun i : Fin (h + 1) ⊕ Fin s =>
        Fin.cast (by omega : h + 1 + s = h + s + 1) (finSumFinEquiv i))).submatrix
      Sum.inr Sum.inr = jacobiMatrix s (fun _ => 0) (fun _ => c) := by
  apply Matrix.ext
  intro i j
  have hi : ¬ h + 1 + i.val < h + 1 := by omega
  have hj : ¬ h + 1 + j.val < h + 1 := by omega
  have he : (h + 1 + i.val + 1 = h + 1 + j.val) ↔ i.val + 1 = j.val := by omega
  have he' : (h + 1 + j.val + 1 = h + 1 + i.val) ↔ j.val + 1 = i.val := by omega
  simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, Fin.val_cast,
    Fin.val_natAdd, headTailMatrix, hi, false_and, dite_false, he, he', jacobiMatrix]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, ite_or]

noncomputable def headTailPolynomial (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (s : ℕ) : Polynomial ℝ :=
  (headTailMatrix h A c s).charpoly

theorem headTailPolynomial_recurrence (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (s : ℕ) :
    headTailPolynomial h A c (s + 2) =
      Polynomial.X * headTailPolynomial h A c (s + 1) -
        Polynomial.C (c ^ 2) * headTailPolynomial h A c s := by
  unfold headTailPolynomial
  rw [headTailMatrix_succ_border, pathBorder_charpoly]
  rw [headTailMatrix_prefix]
  simp

end KadarYu
