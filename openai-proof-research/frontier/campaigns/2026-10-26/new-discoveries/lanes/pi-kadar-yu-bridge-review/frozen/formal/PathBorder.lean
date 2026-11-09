/-
The determinant expansion adapts the proof of `extendPath_det` in
Mathlib/LinearAlgebra/Matrix/Cartan/Basic.lean (Apache 2.0), generalizing its
integer diagonal 2 and coupling -1 to arbitrary scalars in a commutative ring.
This is classical supporting infrastructure, with no discovery credit.
-/
import JacobiSimple

namespace KadarYu

open Matrix Polynomial

def pathBorder {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (d c : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  let tailLink := fun i : Fin n => if i.val + 1 = n then c else 0
  fun i j => Fin.lastCases (Fin.lastCases d tailLink j)
    (fun i => Fin.lastCases (tailLink i) (fun j => M i j) j) i

@[simp]
theorem pathBorder_last_last {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (d c : R) :
    pathBorder M d c (Fin.last n) (Fin.last n) = d := by
  simp [pathBorder]

@[simp]
theorem pathBorder_last_cast {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (d c : R) (j : Fin n) :
    pathBorder M d c (Fin.last n) j.castSucc =
      if j.val + 1 = n then c else 0 := by
  simp [pathBorder]

@[simp]
theorem pathBorder_cast_last {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (d c : R) (i : Fin n) :
    pathBorder M d c i.castSucc (Fin.last n) =
      if i.val + 1 = n then c else 0 := by
  simp [pathBorder]

@[simp]
theorem pathBorder_cast_cast {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (d c : R) (i j : Fin n) :
    pathBorder M d c i.castSucc j.castSucc = M i j := by
  simp [pathBorder]

theorem pathBorder_prefix {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (d c : R) :
    (pathBorder M d c).submatrix Fin.castSucc Fin.castSucc = M := by
  ext i j
  simp [Matrix.submatrix_apply]

theorem pathBorder_minor {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (d c : R) :
    ((pathBorder M d c).submatrix Fin.castSucc
      (Fin.succAbove (Fin.castSucc (Fin.last n)))).det =
        c * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  let B := (pathBorder M d c).submatrix Fin.castSucc
    (Fin.succAbove (Fin.castSucc (Fin.last n)))
  have hlast : B (Fin.last n) (Fin.last n) = c := by
    simp [B, Matrix.submatrix_apply]
  have hzero (i : Fin n) : B i.castSucc (Fin.last n) = 0 := by
    simp [B, Matrix.submatrix_apply]
    omega
  have hminor : B.submatrix Fin.castSucc Fin.castSucc =
      M.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp [B, Matrix.submatrix_apply]
  change B.det = _
  simp [Matrix.det_succ_column B (Fin.last n), Fin.sum_univ_castSucc,
    hlast, hzero, hminor]

theorem pathBorder_det {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (d c : R) :
    (pathBorder M d c).det =
      d * M.det - c ^ 2 * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row (pathBorder M d c) (Fin.last _), Fin.sum_univ_castSucc]
  simp only [pathBorder_last_last, pathBorder_last_cast,
    Fin.val_last, Fin.succAbove_last, pathBorder_prefix]
  rw [Finset.sum_eq_single_of_mem (Fin.last n) (Finset.mem_univ _)]
  · rw [ite_eq_left (by rfl), pathBorder_minor, Fin.val_castSucc, Fin.val_last,
      Odd.neg_one_pow ⟨n, by ring⟩, Even.neg_one_pow ⟨n + 1, rfl⟩]
    ring
  · intro b _ hb
    rw [ite_eq_right (fun h => hb (Fin.ext (by rw [Fin.val_last]; omega)))]
    ring

theorem charmatrix_pathBorder {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (d c : ℝ) :
    (pathBorder M d c).charmatrix =
      pathBorder M.charmatrix (X - C d) (-C c) := by
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) j) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · have hne : Fin.last n ≠ j.castSucc := by
        intro h
        have he := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_castSucc] at he
        omega
      simp only [Matrix.charmatrix_apply_ne _ _ _ hne, pathBorder_last_cast]
      split_ifs <;> simp
  · simp
    split_ifs <;> simp_all
  · by_cases h : i = j
    · subst j
      simp
    · simp [h]

theorem charmatrix_prefix {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    M.charmatrix.submatrix Fin.castSucc Fin.castSucc =
      (M.submatrix Fin.castSucc Fin.castSucc).charmatrix := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [Matrix.submatrix_apply]
  · have h' : i.castSucc ≠ j.castSucc := fun he => h (Fin.castSucc_injective _ he)
    simp [Matrix.submatrix_apply, Matrix.charmatrix_apply_ne, h, h']

theorem pathBorder_charpoly {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (d c : ℝ) :
    (pathBorder M d c).charpoly =
      (X - C d) * M.charpoly - C (c ^ 2) *
        (M.submatrix Fin.castSucc Fin.castSucc).charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_pathBorder, pathBorder_det, charmatrix_prefix]
  simp

theorem unitPath_charpoly_recurrence {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (pathBorder M 0 1).charpoly =
      X * M.charpoly - (M.submatrix Fin.castSucc Fin.castSucc).charpoly := by
  simpa using pathBorder_charpoly M 0 1

end KadarYu
