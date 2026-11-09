import VerifiedDet
namespace Nut8.NewCertificates0000
def C0 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate0 : C0.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction0 : ¬ (C0.det = 0 ∧ ∀ i, C0.adjugate i i ≠ 0) := by
  intro h
  have := certificate0
  rw [h.1] at this
  norm_num at this
def C1 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1 : C1.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1 : ¬ (C1.det = 0 ∧ ∀ i, C1.adjugate i i ≠ 0) := by
  intro h
  have := certificate1
  rw [h.1] at this
  norm_num at this
def C2 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2 : C2.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2 : ¬ (C2.det = 0 ∧ ∀ i, C2.adjugate i i ≠ 0) := by
  intro h
  have := certificate2
  rw [h.1] at this
  norm_num at this
def C3 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate3 : C3.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3 : ¬ (C3.det = 0 ∧ ∀ i, C3.adjugate i i ≠ 0) := by
  intro h
  have := certificate3
  rw [h.1] at this
  norm_num at this
def C4 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate4 : C4.det = (-80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4 : ¬ (C4.det = 0 ∧ ∀ i, C4.adjugate i i ≠ 0) := by
  intro h
  have := certificate4
  rw [h.1] at this
  norm_num at this
def C5 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5 : C5.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5 : ¬ (C5.det = 0 ∧ ∀ i, C5.adjugate i i ≠ 0) := by
  intro h
  have := certificate5
  rw [h.1] at this
  norm_num at this
def C6 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate6 : C6.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6 : ¬ (C6.det = 0 ∧ ∀ i, C6.adjugate i i ≠ 0) := by
  intro h
  have := certificate6
  rw [h.1] at this
  norm_num at this
def C7 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate7 : C7.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7 : ¬ (C7.det = 0 ∧ ∀ i, C7.adjugate i i ≠ 0) := by
  intro h
  have := certificate7
  rw [h.1] at this
  norm_num at this
def C8 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate8 : C8.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8 : ¬ (C8.det = 0 ∧ ∀ i, C8.adjugate i i ≠ 0) := by
  intro h
  have := certificate8
  rw [h.1] at this
  norm_num at this
def C9 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate9 : C9.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9 : ¬ (C9.det = 0 ∧ ∀ i, C9.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate9
def C10 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate10 : C10.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction10 : ¬ (C10.det = 0 ∧ ∀ i, C10.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate10
def C11 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate11 : C11.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction11 : ¬ (C11.det = 0 ∧ ∀ i, C11.adjugate i i ≠ 0) := by
  intro h
  have := certificate11
  rw [h.1] at this
  norm_num at this
def C12 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate12 : C12.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction12 : ¬ (C12.det = 0 ∧ ∀ i, C12.adjugate i i ≠ 0) := by
  intro h
  have := certificate12
  rw [h.1] at this
  norm_num at this
def C13 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate13 : C13.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction13 : ¬ (C13.det = 0 ∧ ∀ i, C13.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate13
def C14 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate14 : C14.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction14 : ¬ (C14.det = 0 ∧ ∀ i, C14.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate14
def C15 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate15 : C15.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction15 : ¬ (C15.det = 0 ∧ ∀ i, C15.adjugate i i ≠ 0) := by
  intro h
  have := certificate15
  rw [h.1] at this
  norm_num at this
def C16 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate16 : C16.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction16 : ¬ (C16.det = 0 ∧ ∀ i, C16.adjugate i i ≠ 0) := by
  intro h
  have := certificate16
  rw [h.1] at this
  norm_num at this
def C17 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate17 : C17.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction17 : ¬ (C17.det = 0 ∧ ∀ i, C17.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate17
def C18 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate18 : C18.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction18 : ¬ (C18.det = 0 ∧ ∀ i, C18.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate18
def C19 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate19 : C19.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction19 : ¬ (C19.det = 0 ∧ ∀ i, C19.adjugate i i ≠ 0) := by
  intro h
  have := certificate19
  rw [h.1] at this
  norm_num at this
def C20 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate20 : C20.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction20 : ¬ (C20.det = 0 ∧ ∀ i, C20.adjugate i i ≠ 0) := by
  intro h
  have := certificate20
  rw [h.1] at this
  norm_num at this
def C21 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate21 : C21.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction21 : ¬ (C21.det = 0 ∧ ∀ i, C21.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate21
def C22 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate22 : C22.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction22 : ¬ (C22.det = 0 ∧ ∀ i, C22.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate22
def C23 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate23 : C23.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction23 : ¬ (C23.det = 0 ∧ ∀ i, C23.adjugate i i ≠ 0) := by
  intro h
  have := certificate23
  rw [h.1] at this
  norm_num at this
def C24 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate24 : C24.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction24 : ¬ (C24.det = 0 ∧ ∀ i, C24.adjugate i i ≠ 0) := by
  intro h
  have := certificate24
  rw [h.1] at this
  norm_num at this
def C25 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate25 : C25.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction25 : ¬ (C25.det = 0 ∧ ∀ i, C25.adjugate i i ≠ 0) := by
  intro h
  have := certificate25
  rw [h.1] at this
  norm_num at this
def C26 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate26 : C26.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction26 : ¬ (C26.det = 0 ∧ ∀ i, C26.adjugate i i ≠ 0) := by
  intro h
  have := certificate26
  rw [h.1] at this
  norm_num at this
def C27 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate27 : C27.det = (-80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction27 : ¬ (C27.det = 0 ∧ ∀ i, C27.adjugate i i ≠ 0) := by
  intro h
  have := certificate27
  rw [h.1] at this
  norm_num at this
def C28 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate28 : C28.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction28 : ¬ (C28.det = 0 ∧ ∀ i, C28.adjugate i i ≠ 0) := by
  intro h
  have := certificate28
  rw [h.1] at this
  norm_num at this
def C29 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate29 : C29.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction29 : ¬ (C29.det = 0 ∧ ∀ i, C29.adjugate i i ≠ 0) := by
  intro h
  have := certificate29
  rw [h.1] at this
  norm_num at this
def C30 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate30 : C30.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction30 : ¬ (C30.det = 0 ∧ ∀ i, C30.adjugate i i ≠ 0) := by
  intro h
  have := certificate30
  rw [h.1] at this
  norm_num at this
def C31 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate31 : C31.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction31 : ¬ (C31.det = 0 ∧ ∀ i, C31.adjugate i i ≠ 0) := by
  intro h
  have := certificate31
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0000
