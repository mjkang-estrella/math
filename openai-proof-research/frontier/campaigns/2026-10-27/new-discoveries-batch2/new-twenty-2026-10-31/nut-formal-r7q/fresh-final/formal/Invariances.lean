import FiniteGrammar
namespace Nut8
/-- Structural overapproximation: only the epsilon positivity condition is discarded. -/
def Structural (C : QuotientMatrix) (s : ℤ) : Prop := Admissible C (-1) s

theorem admissible_structural (C : QuotientMatrix) (ε s : ℤ)
    (h : Admissible C ε s) : Structural C s := by
  rcases h with ⟨_, hs, hsym, hrow, hbound, hdiag, _, hconn⟩
  exact ⟨Or.inr rfl, hs, hsym, hrow, hbound, hdiag, by omega, hconn⟩

def switch {n : ℕ} (d : Fin n → ℤ) (C : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => d i * C i j * d j

theorem switch_diagonal {n : ℕ} (d : Fin n → ℤ)
    (C : Matrix (Fin n) (Fin n) ℤ) :
    switch d C = Matrix.diagonal d * C * Matrix.diagonal d := by
  ext i j
  simp [switch, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem switch_det {n : ℕ} (d : Fin n → ℤ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) (C : Matrix (Fin n) (Fin n) ℤ) :
    (switch d C).det = C.det := by
  rw [switch_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have h : (∏ i, d i) * (∏ i, d i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    rcases hd i with hi | hi <;> simp [hi]
  calc
    (∏ i, d i) * C.det * (∏ i, d i) = C.det * ((∏ i, d i) * (∏ i, d i)) := by ring
    _ = C.det := by rw [h, mul_one]

theorem switch_principal {n : ℕ} (d : Fin (n+1) → ℤ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) (C : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
    (i : Fin (n+1)) : (switch d C).adjugate i i = C.adjugate i i := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.adjugate_fin_succ_eq_det_submatrix]
  congr 1
  change (switch (d ∘ i.succAbove) (C.submatrix i.succAbove i.succAbove)).det = _
  exact switch_det _ (fun j => hd (i.succAbove j)) _

 theorem switch_abs {n : ℕ} (d : Fin n → ℤ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) (C : Matrix (Fin n) (Fin n) ℤ) (i j) :
    |switch d C i j| = |C i j| := by
  rcases hd i with hi | hi <;> rcases hd j with hj | hj <;>
    simp [switch, hi, hj]

 theorem switch_diag {n : ℕ} (d : Fin n → ℤ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) (C : Matrix (Fin n) (Fin n) ℤ) (i) :
    switch d C i i = C i i := by
  rcases hd i with hi | hi <;> simp [switch, hi]

theorem structural_switch (d : Fin 8 → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1)
    (C : QuotientMatrix) (s : ℤ) (h : Structural C s) : Structural (switch d C) s := by
  rcases h with ⟨he, hs, hsym, hrow, hbound, hdiag, _, hconn⟩
  refine ⟨he, hs, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · intro i j
    dsimp [switch]
    rw [hsym i j]
    ring
  · intro i
    simpa only [switch_abs d hd] using hrow i
  · intro i j
    simpa only [switch_abs d hd] using hbound i j
  · intro i
    simpa only [switch_diag d hd] using hdiag i
  · intro S hS hS'
    obtain ⟨i, hi, j, hj, hij⟩ := hconn S hS hS'
    refine ⟨i, hi, j, hj, ?_⟩
    rcases hd i with hi' | hi' <;> rcases hd j with hj' | hj' <;>
      simpa [switch, hi', hj'] using hij
theorem support_relabel (e : Equiv.Perm (Fin 8)) (C : QuotientMatrix)
    (h : SupportConnected C) : SupportConnected (C.submatrix e e) := by
  intro S hS hS'
  have hne : (S.image e).Nonempty := hS.image e
  have hproper : S.image e ≠ Finset.univ := by
    intro heq
    apply hS'
    apply Finset.eq_univ_of_forall
    intro i
    have hi : e i ∈ S.image e := by rw [heq]; exact Finset.mem_univ _
    simpa only [Finset.mem_image, e.injective.eq_iff, exists_eq_right] using hi
  obtain ⟨i, hi, j, hj, hij⟩ := h (S.image e) hne hproper
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
  refine ⟨a, ha, e.symm j, ?_, ?_⟩
  · intro hb
    exact hj (Finset.mem_image.mpr ⟨e.symm j, hb, e.apply_symm_apply j⟩)
  · simpa using hij

theorem admissible_relabel (e : Equiv.Perm (Fin 8)) (C : QuotientMatrix) (ε s : ℤ)
    (h : Admissible C ε s) : Admissible (C.submatrix e e) ε s := by
  rcases h with ⟨he, hs, hsym, hrow, hbound, hdiag, hpos, hconn⟩
  refine ⟨he, hs, ?_, ?_, ?_, ?_, ?_, support_relabel e C hconn⟩
  · intro i j; exact hsym (e i) (e j)
  · intro i
    change ∑ j, |C (e i) (e j)| = 3
    rw [Equiv.sum_comp e (fun j => |C (e i) j|)]
    exact hrow (e i)
  · intro i j; exact hbound (e i) (e j)
  · intro i; exact hdiag (e i)
  · intro he i j; exact hpos he (e i) (e j)

theorem relabel_principal {n : ℕ} (e : Equiv.Perm (Fin n))
    (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (C.submatrix e e).adjugate i i = C.adjugate (e i) (e i) := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℤ => A i i) (Matrix.adjugate_submatrix_equiv_self e C)
  simpa only [Matrix.submatrix_apply] using h

/-- Refutation of a switched representative transports to the original matrix. -/
theorem obstruction_of_switch (d : Fin 8 → ℤ) (hd : ∀ i, d i = 1 ∨ d i = -1)
    (C : QuotientMatrix)
    (h : ¬ ((switch d C).det = 0 ∧ ∀ i, (switch d C).adjugate i i ≠ 0)) :
    ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0) := by
  simpa only [switch_det d hd, switch_principal d hd] using h

theorem obstruction_of_relabel (e : Equiv.Perm (Fin 8)) (C : QuotientMatrix)
    (h : ¬ ((C.submatrix e e).det = 0 ∧ ∀ i, (C.submatrix e e).adjugate i i ≠ 0)) :
    ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0) := by
  intro ⟨hdet, hcof⟩
  apply h
  exact ⟨by simpa only [Matrix.det_submatrix_equiv_self] using hdet,
    fun i => by simpa only [relabel_principal] using hcof (e i)⟩
end Nut8
