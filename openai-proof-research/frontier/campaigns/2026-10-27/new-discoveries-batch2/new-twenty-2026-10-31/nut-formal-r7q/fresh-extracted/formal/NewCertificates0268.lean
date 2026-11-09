import VerifiedDet
namespace Nut8.NewCertificates0268
def C8576 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8576 : C8576.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8576 : ¬ (C8576.det = 0 ∧ ∀ i, C8576.adjugate i i ≠ 0) := by
  intro h
  have := certificate8576
  rw [h.1] at this
  norm_num at this
def C8577 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8577 : C8577.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8577 : ¬ (C8577.det = 0 ∧ ∀ i, C8577.adjugate i i ≠ 0) := by
  intro h
  have := certificate8577
  rw [h.1] at this
  norm_num at this
def C8578 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8578 : C8578.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8578 : ¬ (C8578.det = 0 ∧ ∀ i, C8578.adjugate i i ≠ 0) := by
  intro h
  have := certificate8578
  rw [h.1] at this
  norm_num at this
def C8579 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8579 : C8579.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8579 : ¬ (C8579.det = 0 ∧ ∀ i, C8579.adjugate i i ≠ 0) := by
  intro h
  have := certificate8579
  rw [h.1] at this
  norm_num at this
def C8580 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8580 : C8580.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8580 : ¬ (C8580.det = 0 ∧ ∀ i, C8580.adjugate i i ≠ 0) := by
  intro h
  have := certificate8580
  rw [h.1] at this
  norm_num at this
def C8581 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8581 : C8581.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8581 : ¬ (C8581.det = 0 ∧ ∀ i, C8581.adjugate i i ≠ 0) := by
  intro h
  have := certificate8581
  rw [h.1] at this
  norm_num at this
def C8582 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8582 : C8582.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8582 : ¬ (C8582.det = 0 ∧ ∀ i, C8582.adjugate i i ≠ 0) := by
  intro h
  have := certificate8582
  rw [h.1] at this
  norm_num at this
def C8583 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8583 : C8583.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8583 : ¬ (C8583.det = 0 ∧ ∀ i, C8583.adjugate i i ≠ 0) := by
  intro h
  have := certificate8583
  rw [h.1] at this
  norm_num at this
def C8584 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8584 : C8584.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8584 : ¬ (C8584.det = 0 ∧ ∀ i, C8584.adjugate i i ≠ 0) := by
  intro h
  have := certificate8584
  rw [h.1] at this
  norm_num at this
def C8585 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8585 : C8585.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8585 : ¬ (C8585.det = 0 ∧ ∀ i, C8585.adjugate i i ≠ 0) := by
  intro h
  have := certificate8585
  rw [h.1] at this
  norm_num at this
def C8586 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8586 : C8586.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8586 : ¬ (C8586.det = 0 ∧ ∀ i, C8586.adjugate i i ≠ 0) := by
  intro h
  have := certificate8586
  rw [h.1] at this
  norm_num at this
def C8587 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8587 : C8587.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8587 : ¬ (C8587.det = 0 ∧ ∀ i, C8587.adjugate i i ≠ 0) := by
  intro h
  have := certificate8587
  rw [h.1] at this
  norm_num at this
def C8588 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8588 : C8588.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8588 : ¬ (C8588.det = 0 ∧ ∀ i, C8588.adjugate i i ≠ 0) := by
  intro h
  have := certificate8588
  rw [h.1] at this
  norm_num at this
def C8589 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8589 : C8589.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8589 : ¬ (C8589.det = 0 ∧ ∀ i, C8589.adjugate i i ≠ 0) := by
  intro h
  have := certificate8589
  rw [h.1] at this
  norm_num at this
def C8590 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8590 : C8590.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8590 : ¬ (C8590.det = 0 ∧ ∀ i, C8590.adjugate i i ≠ 0) := by
  intro h
  have := certificate8590
  rw [h.1] at this
  norm_num at this
def C8591 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8591 : C8591.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8591 : ¬ (C8591.det = 0 ∧ ∀ i, C8591.adjugate i i ≠ 0) := by
  intro h
  have := certificate8591
  rw [h.1] at this
  norm_num at this
def C8592 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8592 : C8592.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8592 : ¬ (C8592.det = 0 ∧ ∀ i, C8592.adjugate i i ≠ 0) := by
  intro h
  have := certificate8592
  rw [h.1] at this
  norm_num at this
def C8593 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8593 : C8593.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8593 : ¬ (C8593.det = 0 ∧ ∀ i, C8593.adjugate i i ≠ 0) := by
  intro h
  have := certificate8593
  rw [h.1] at this
  norm_num at this
def C8594 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8594 : C8594.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8594 : ¬ (C8594.det = 0 ∧ ∀ i, C8594.adjugate i i ≠ 0) := by
  intro h
  have := certificate8594
  rw [h.1] at this
  norm_num at this
def C8595 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8595 : C8595.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8595 : ¬ (C8595.det = 0 ∧ ∀ i, C8595.adjugate i i ≠ 0) := by
  intro h
  have := certificate8595
  rw [h.1] at this
  norm_num at this
def C8596 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8596 : C8596.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8596 : ¬ (C8596.det = 0 ∧ ∀ i, C8596.adjugate i i ≠ 0) := by
  intro h
  have := certificate8596
  rw [h.1] at this
  norm_num at this
def C8597 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8597 : C8597.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8597 : ¬ (C8597.det = 0 ∧ ∀ i, C8597.adjugate i i ≠ 0) := by
  intro h
  have := certificate8597
  rw [h.1] at this
  norm_num at this
def C8598 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8598 : C8598.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8598 : ¬ (C8598.det = 0 ∧ ∀ i, C8598.adjugate i i ≠ 0) := by
  intro h
  have := certificate8598
  rw [h.1] at this
  norm_num at this
def C8599 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8599 : C8599.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8599 : ¬ (C8599.det = 0 ∧ ∀ i, C8599.adjugate i i ≠ 0) := by
  intro h
  have := certificate8599
  rw [h.1] at this
  norm_num at this
def C8600 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8600 : C8600.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8600 : ¬ (C8600.det = 0 ∧ ∀ i, C8600.adjugate i i ≠ 0) := by
  intro h
  have := certificate8600
  rw [h.1] at this
  norm_num at this
def C8601 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8601 : C8601.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8601 : ¬ (C8601.det = 0 ∧ ∀ i, C8601.adjugate i i ≠ 0) := by
  intro h
  have := certificate8601
  rw [h.1] at this
  norm_num at this
def C8602 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8602 : C8602.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8602 : ¬ (C8602.det = 0 ∧ ∀ i, C8602.adjugate i i ≠ 0) := by
  intro h
  have := certificate8602
  rw [h.1] at this
  norm_num at this
def C8603 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8603 : C8603.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8603 : ¬ (C8603.det = 0 ∧ ∀ i, C8603.adjugate i i ≠ 0) := by
  intro h
  have := certificate8603
  rw [h.1] at this
  norm_num at this
def C8604 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8604 : C8604.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8604 : ¬ (C8604.det = 0 ∧ ∀ i, C8604.adjugate i i ≠ 0) := by
  intro h
  have := certificate8604
  rw [h.1] at this
  norm_num at this
def C8605 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8605 : C8605.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8605 : ¬ (C8605.det = 0 ∧ ∀ i, C8605.adjugate i i ≠ 0) := by
  intro h
  have := certificate8605
  rw [h.1] at this
  norm_num at this
def C8606 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8606 : C8606.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8606 : ¬ (C8606.det = 0 ∧ ∀ i, C8606.adjugate i i ≠ 0) := by
  intro h
  have := certificate8606
  rw [h.1] at this
  norm_num at this
def C8607 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8607 : C8607.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8607 : ¬ (C8607.det = 0 ∧ ∀ i, C8607.adjugate i i ≠ 0) := by
  intro h
  have := certificate8607
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0268
