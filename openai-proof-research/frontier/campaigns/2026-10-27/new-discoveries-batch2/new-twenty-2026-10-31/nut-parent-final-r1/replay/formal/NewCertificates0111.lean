import VerifiedDet
namespace Nut8.NewCertificates0111
def C3552 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3552 : C3552.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3552 : ¬ (C3552.det = 0 ∧ ∀ i, C3552.adjugate i i ≠ 0) := by
  intro h
  have := certificate3552
  rw [h.1] at this
  norm_num at this
def C3553 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3553 : C3553.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3553 : ¬ (C3553.det = 0 ∧ ∀ i, C3553.adjugate i i ≠ 0) := by
  intro h
  have := certificate3553
  rw [h.1] at this
  norm_num at this
def C3554 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3554 : C3554.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3554 : ¬ (C3554.det = 0 ∧ ∀ i, C3554.adjugate i i ≠ 0) := by
  intro h
  have := certificate3554
  rw [h.1] at this
  norm_num at this
def C3555 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3555 : C3555.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3555 : ¬ (C3555.det = 0 ∧ ∀ i, C3555.adjugate i i ≠ 0) := by
  intro h
  have := certificate3555
  rw [h.1] at this
  norm_num at this
def C3556 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3556 : C3556.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3556 : ¬ (C3556.det = 0 ∧ ∀ i, C3556.adjugate i i ≠ 0) := by
  intro h
  have := certificate3556
  rw [h.1] at this
  norm_num at this
def C3557 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3557 : C3557.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3557 : ¬ (C3557.det = 0 ∧ ∀ i, C3557.adjugate i i ≠ 0) := by
  intro h
  have := certificate3557
  rw [h.1] at this
  norm_num at this
def C3558 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3558 : C3558.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3558 : ¬ (C3558.det = 0 ∧ ∀ i, C3558.adjugate i i ≠ 0) := by
  intro h
  have := certificate3558
  rw [h.1] at this
  norm_num at this
def C3559 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3559 : C3559.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3559 : ¬ (C3559.det = 0 ∧ ∀ i, C3559.adjugate i i ≠ 0) := by
  intro h
  have := certificate3559
  rw [h.1] at this
  norm_num at this
def C3560 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3560 : C3560.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3560 : ¬ (C3560.det = 0 ∧ ∀ i, C3560.adjugate i i ≠ 0) := by
  intro h
  have := certificate3560
  rw [h.1] at this
  norm_num at this
def C3561 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3561 : C3561.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3561 : ¬ (C3561.det = 0 ∧ ∀ i, C3561.adjugate i i ≠ 0) := by
  intro h
  have := certificate3561
  rw [h.1] at this
  norm_num at this
def C3562 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3562 : C3562.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3562 : ¬ (C3562.det = 0 ∧ ∀ i, C3562.adjugate i i ≠ 0) := by
  intro h
  have := certificate3562
  rw [h.1] at this
  norm_num at this
def C3563 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3563 : C3563.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3563 : ¬ (C3563.det = 0 ∧ ∀ i, C3563.adjugate i i ≠ 0) := by
  intro h
  have := certificate3563
  rw [h.1] at this
  norm_num at this
def C3564 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3564 : C3564.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3564 : ¬ (C3564.det = 0 ∧ ∀ i, C3564.adjugate i i ≠ 0) := by
  intro h
  have := certificate3564
  rw [h.1] at this
  norm_num at this
def C3565 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3565 : C3565.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3565 : ¬ (C3565.det = 0 ∧ ∀ i, C3565.adjugate i i ≠ 0) := by
  intro h
  have := certificate3565
  rw [h.1] at this
  norm_num at this
def C3566 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3566 : C3566.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3566 : ¬ (C3566.det = 0 ∧ ∀ i, C3566.adjugate i i ≠ 0) := by
  intro h
  have := certificate3566
  rw [h.1] at this
  norm_num at this
def C3567 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3567 : C3567.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3567 : ¬ (C3567.det = 0 ∧ ∀ i, C3567.adjugate i i ≠ 0) := by
  intro h
  have := certificate3567
  rw [h.1] at this
  norm_num at this
def C3568 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3568 : C3568.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3568 : ¬ (C3568.det = 0 ∧ ∀ i, C3568.adjugate i i ≠ 0) := by
  intro h
  have := certificate3568
  rw [h.1] at this
  norm_num at this
def C3569 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3569 : C3569.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3569 : ¬ (C3569.det = 0 ∧ ∀ i, C3569.adjugate i i ≠ 0) := by
  intro h
  have := certificate3569
  rw [h.1] at this
  norm_num at this
def C3570 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3570 : C3570.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3570 : ¬ (C3570.det = 0 ∧ ∀ i, C3570.adjugate i i ≠ 0) := by
  intro h
  have := certificate3570
  rw [h.1] at this
  norm_num at this
def C3571 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3571 : C3571.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3571 : ¬ (C3571.det = 0 ∧ ∀ i, C3571.adjugate i i ≠ 0) := by
  intro h
  have := certificate3571
  rw [h.1] at this
  norm_num at this
def C3572 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3572 : C3572.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3572 : ¬ (C3572.det = 0 ∧ ∀ i, C3572.adjugate i i ≠ 0) := by
  intro h
  have := certificate3572
  rw [h.1] at this
  norm_num at this
def C3573 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3573 : C3573.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3573 : ¬ (C3573.det = 0 ∧ ∀ i, C3573.adjugate i i ≠ 0) := by
  intro h
  have := certificate3573
  rw [h.1] at this
  norm_num at this
def C3574 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate3574 : C3574.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3574 : ¬ (C3574.det = 0 ∧ ∀ i, C3574.adjugate i i ≠ 0) := by
  intro h
  have := certificate3574
  rw [h.1] at this
  norm_num at this
def C3575 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate3575 : C3575.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3575 : ¬ (C3575.det = 0 ∧ ∀ i, C3575.adjugate i i ≠ 0) := by
  intro h
  have := certificate3575
  rw [h.1] at this
  norm_num at this
def C3576 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate3576 : C3576.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3576 : ¬ (C3576.det = 0 ∧ ∀ i, C3576.adjugate i i ≠ 0) := by
  intro h
  have := certificate3576
  rw [h.1] at this
  norm_num at this
def C3577 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate3577 : C3577.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3577 : ¬ (C3577.det = 0 ∧ ∀ i, C3577.adjugate i i ≠ 0) := by
  intro h
  have := certificate3577
  rw [h.1] at this
  norm_num at this
def C3578 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3578 : C3578.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3578 : ¬ (C3578.det = 0 ∧ ∀ i, C3578.adjugate i i ≠ 0) := by
  intro h
  have := certificate3578
  rw [h.1] at this
  norm_num at this
def C3579 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3579 : C3579.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3579 : ¬ (C3579.det = 0 ∧ ∀ i, C3579.adjugate i i ≠ 0) := by
  intro h
  have := certificate3579
  rw [h.1] at this
  norm_num at this
def C3580 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3580 : C3580.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3580 : ¬ (C3580.det = 0 ∧ ∀ i, C3580.adjugate i i ≠ 0) := by
  intro h
  have := certificate3580
  rw [h.1] at this
  norm_num at this
def C3581 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3581 : C3581.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3581 : ¬ (C3581.det = 0 ∧ ∀ i, C3581.adjugate i i ≠ 0) := by
  intro h
  have := certificate3581
  rw [h.1] at this
  norm_num at this
def C3582 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate3582 : C3582.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3582 : ¬ (C3582.det = 0 ∧ ∀ i, C3582.adjugate i i ≠ 0) := by
  intro h
  have := certificate3582
  rw [h.1] at this
  norm_num at this
def C3583 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate3583 : C3583.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3583 : ¬ (C3583.det = 0 ∧ ∀ i, C3583.adjugate i i ≠ 0) := by
  intro h
  have := certificate3583
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0111
