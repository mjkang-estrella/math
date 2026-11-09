import VerifiedDet
namespace Nut8.NewCertificates0112
def C3584 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate3584 : C3584.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3584 : ¬ (C3584.det = 0 ∧ ∀ i, C3584.adjugate i i ≠ 0) := by
  intro h
  have := certificate3584
  rw [h.1] at this
  norm_num at this
def C3585 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate3585 : C3585.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3585 : ¬ (C3585.det = 0 ∧ ∀ i, C3585.adjugate i i ≠ 0) := by
  intro h
  have := certificate3585
  rw [h.1] at this
  norm_num at this
def C3586 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3586 : C3586.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3586 : ¬ (C3586.det = 0 ∧ ∀ i, C3586.adjugate i i ≠ 0) := by
  intro h
  have := certificate3586
  rw [h.1] at this
  norm_num at this
def C3587 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3587 : C3587.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3587 : ¬ (C3587.det = 0 ∧ ∀ i, C3587.adjugate i i ≠ 0) := by
  intro h
  have := certificate3587
  rw [h.1] at this
  norm_num at this
def C3588 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3588 : C3588.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3588 : ¬ (C3588.det = 0 ∧ ∀ i, C3588.adjugate i i ≠ 0) := by
  intro h
  have := certificate3588
  rw [h.1] at this
  norm_num at this
def C3589 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3589 : C3589.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3589 : ¬ (C3589.det = 0 ∧ ∀ i, C3589.adjugate i i ≠ 0) := by
  intro h
  have := certificate3589
  rw [h.1] at this
  norm_num at this
def C3590 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate3590 : C3590.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3590 : ¬ (C3590.det = 0 ∧ ∀ i, C3590.adjugate i i ≠ 0) := by
  intro h
  have := certificate3590
  rw [h.1] at this
  norm_num at this
def C3591 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate3591 : C3591.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3591 : ¬ (C3591.det = 0 ∧ ∀ i, C3591.adjugate i i ≠ 0) := by
  intro h
  have := certificate3591
  rw [h.1] at this
  norm_num at this
def C3592 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate3592 : C3592.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3592 : ¬ (C3592.det = 0 ∧ ∀ i, C3592.adjugate i i ≠ 0) := by
  intro h
  have := certificate3592
  rw [h.1] at this
  norm_num at this
def C3593 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate3593 : C3593.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3593 : ¬ (C3593.det = 0 ∧ ∀ i, C3593.adjugate i i ≠ 0) := by
  intro h
  have := certificate3593
  rw [h.1] at this
  norm_num at this
def C3594 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3594 : C3594.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3594 : ¬ (C3594.det = 0 ∧ ∀ i, C3594.adjugate i i ≠ 0) := by
  intro h
  have := certificate3594
  rw [h.1] at this
  norm_num at this
def C3595 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3595 : C3595.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3595 : ¬ (C3595.det = 0 ∧ ∀ i, C3595.adjugate i i ≠ 0) := by
  intro h
  have := certificate3595
  rw [h.1] at this
  norm_num at this
def C3596 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3596 : C3596.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3596 : ¬ (C3596.det = 0 ∧ ∀ i, C3596.adjugate i i ≠ 0) := by
  intro h
  have := certificate3596
  rw [h.1] at this
  norm_num at this
def C3597 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3597 : C3597.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3597 : ¬ (C3597.det = 0 ∧ ∀ i, C3597.adjugate i i ≠ 0) := by
  intro h
  have := certificate3597
  rw [h.1] at this
  norm_num at this
def C3598 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate3598 : C3598.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3598 : ¬ (C3598.det = 0 ∧ ∀ i, C3598.adjugate i i ≠ 0) := by
  intro h
  have := certificate3598
  rw [h.1] at this
  norm_num at this
def C3599 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate3599 : C3599.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3599 : ¬ (C3599.det = 0 ∧ ∀ i, C3599.adjugate i i ≠ 0) := by
  intro h
  have := certificate3599
  rw [h.1] at this
  norm_num at this
def C3600 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate3600 : C3600.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3600 : ¬ (C3600.det = 0 ∧ ∀ i, C3600.adjugate i i ≠ 0) := by
  intro h
  have := certificate3600
  rw [h.1] at this
  norm_num at this
def C3601 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate3601 : C3601.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3601 : ¬ (C3601.det = 0 ∧ ∀ i, C3601.adjugate i i ≠ 0) := by
  intro h
  have := certificate3601
  rw [h.1] at this
  norm_num at this
def C3602 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3602 : C3602.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3602 : ¬ (C3602.det = 0 ∧ ∀ i, C3602.adjugate i i ≠ 0) := by
  intro h
  have := certificate3602
  rw [h.1] at this
  norm_num at this
def C3603 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3603 : C3603.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3603 : ¬ (C3603.det = 0 ∧ ∀ i, C3603.adjugate i i ≠ 0) := by
  intro h
  have := certificate3603
  rw [h.1] at this
  norm_num at this
def C3604 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3604 : C3604.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3604 : ¬ (C3604.det = 0 ∧ ∀ i, C3604.adjugate i i ≠ 0) := by
  intro h
  have := certificate3604
  rw [h.1] at this
  norm_num at this
def C3605 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3605 : C3605.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3605 : ¬ (C3605.det = 0 ∧ ∀ i, C3605.adjugate i i ≠ 0) := by
  intro h
  have := certificate3605
  rw [h.1] at this
  norm_num at this
def C3606 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3606 : C3606.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3606 : ¬ (C3606.det = 0 ∧ ∀ i, C3606.adjugate i i ≠ 0) := by
  intro h
  have := certificate3606
  rw [h.1] at this
  norm_num at this
def C3607 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3607 : C3607.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3607 : ¬ (C3607.det = 0 ∧ ∀ i, C3607.adjugate i i ≠ 0) := by
  intro h
  have := certificate3607
  rw [h.1] at this
  norm_num at this
def C3608 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3608 : C3608.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3608 : ¬ (C3608.det = 0 ∧ ∀ i, C3608.adjugate i i ≠ 0) := by
  intro h
  have := certificate3608
  rw [h.1] at this
  norm_num at this
def C3609 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3609 : C3609.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3609 : ¬ (C3609.det = 0 ∧ ∀ i, C3609.adjugate i i ≠ 0) := by
  intro h
  have := certificate3609
  rw [h.1] at this
  norm_num at this
def C3610 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate3610 : C3610.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3610 : ¬ (C3610.det = 0 ∧ ∀ i, C3610.adjugate i i ≠ 0) := by
  intro h
  have := certificate3610
  rw [h.1] at this
  norm_num at this
def C3611 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate3611 : C3611.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3611 : ¬ (C3611.det = 0 ∧ ∀ i, C3611.adjugate i i ≠ 0) := by
  intro h
  have := certificate3611
  rw [h.1] at this
  norm_num at this
def C3612 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate3612 : C3612.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3612 : ¬ (C3612.det = 0 ∧ ∀ i, C3612.adjugate i i ≠ 0) := by
  intro h
  have := certificate3612
  rw [h.1] at this
  norm_num at this
def C3613 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate3613 : C3613.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3613 : ¬ (C3613.det = 0 ∧ ∀ i, C3613.adjugate i i ≠ 0) := by
  intro h
  have := certificate3613
  rw [h.1] at this
  norm_num at this
def C3614 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3614 : C3614.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3614 : ¬ (C3614.det = 0 ∧ ∀ i, C3614.adjugate i i ≠ 0) := by
  intro h
  have := certificate3614
  rw [h.1] at this
  norm_num at this
def C3615 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3615 : C3615.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3615 : ¬ (C3615.det = 0 ∧ ∀ i, C3615.adjugate i i ≠ 0) := by
  intro h
  have := certificate3615
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0112
