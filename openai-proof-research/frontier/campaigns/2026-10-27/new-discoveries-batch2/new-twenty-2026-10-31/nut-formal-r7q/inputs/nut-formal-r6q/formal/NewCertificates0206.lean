import VerifiedDet
namespace Nut8.NewCertificates0206
def C6592 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6592 : C6592.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6592 : ¬ (C6592.det = 0 ∧ ∀ i, C6592.adjugate i i ≠ 0) := by
  intro h
  have := certificate6592
  rw [h.1] at this
  norm_num at this
def C6593 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6593 : C6593.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6593 : ¬ (C6593.det = 0 ∧ ∀ i, C6593.adjugate i i ≠ 0) := by
  intro h
  have := certificate6593
  rw [h.1] at this
  norm_num at this
def C6594 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6594 : C6594.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6594 : ¬ (C6594.det = 0 ∧ ∀ i, C6594.adjugate i i ≠ 0) := by
  intro h
  have := certificate6594
  rw [h.1] at this
  norm_num at this
def C6595 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6595 : C6595.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6595 : ¬ (C6595.det = 0 ∧ ∀ i, C6595.adjugate i i ≠ 0) := by
  intro h
  have := certificate6595
  rw [h.1] at this
  norm_num at this
def C6596 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6596 : C6596.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6596 : ¬ (C6596.det = 0 ∧ ∀ i, C6596.adjugate i i ≠ 0) := by
  intro h
  have := certificate6596
  rw [h.1] at this
  norm_num at this
def C6597 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6597 : C6597.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6597 : ¬ (C6597.det = 0 ∧ ∀ i, C6597.adjugate i i ≠ 0) := by
  intro h
  have := certificate6597
  rw [h.1] at this
  norm_num at this
def C6598 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6598 : C6598.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6598 : ¬ (C6598.det = 0 ∧ ∀ i, C6598.adjugate i i ≠ 0) := by
  intro h
  have := certificate6598
  rw [h.1] at this
  norm_num at this
def C6599 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6599 : C6599.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6599 : ¬ (C6599.det = 0 ∧ ∀ i, C6599.adjugate i i ≠ 0) := by
  intro h
  have := certificate6599
  rw [h.1] at this
  norm_num at this
def C6600 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6600 : C6600.det = (-45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6600 : ¬ (C6600.det = 0 ∧ ∀ i, C6600.adjugate i i ≠ 0) := by
  intro h
  have := certificate6600
  rw [h.1] at this
  norm_num at this
def C6601 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6601 : C6601.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6601 : ¬ (C6601.det = 0 ∧ ∀ i, C6601.adjugate i i ≠ 0) := by
  intro h
  have := certificate6601
  rw [h.1] at this
  norm_num at this
def C6602 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6602 : C6602.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6602 : ¬ (C6602.det = 0 ∧ ∀ i, C6602.adjugate i i ≠ 0) := by
  intro h
  have := certificate6602
  rw [h.1] at this
  norm_num at this
def C6603 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6603 : C6603.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6603 : ¬ (C6603.det = 0 ∧ ∀ i, C6603.adjugate i i ≠ 0) := by
  intro h
  have := certificate6603
  rw [h.1] at this
  norm_num at this
def C6604 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6604 : C6604.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6604 : ¬ (C6604.det = 0 ∧ ∀ i, C6604.adjugate i i ≠ 0) := by
  intro h
  have := certificate6604
  rw [h.1] at this
  norm_num at this
def C6605 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6605 : C6605.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6605 : ¬ (C6605.det = 0 ∧ ∀ i, C6605.adjugate i i ≠ 0) := by
  intro h
  have := certificate6605
  rw [h.1] at this
  norm_num at this
def C6606 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6606 : C6606.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6606 : ¬ (C6606.det = 0 ∧ ∀ i, C6606.adjugate i i ≠ 0) := by
  intro h
  have := certificate6606
  rw [h.1] at this
  norm_num at this
def C6607 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6607 : C6607.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6607 : ¬ (C6607.det = 0 ∧ ∀ i, C6607.adjugate i i ≠ 0) := by
  intro h
  have := certificate6607
  rw [h.1] at this
  norm_num at this
def C6608 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6608 : C6608.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6608 : ¬ (C6608.det = 0 ∧ ∀ i, C6608.adjugate i i ≠ 0) := by
  intro h
  have := certificate6608
  rw [h.1] at this
  norm_num at this
def C6609 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6609 : C6609.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6609 : ¬ (C6609.det = 0 ∧ ∀ i, C6609.adjugate i i ≠ 0) := by
  intro h
  have := certificate6609
  rw [h.1] at this
  norm_num at this
def C6610 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6610 : C6610.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6610 : ¬ (C6610.det = 0 ∧ ∀ i, C6610.adjugate i i ≠ 0) := by
  intro h
  have := certificate6610
  rw [h.1] at this
  norm_num at this
def C6611 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6611 : C6611.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6611 : ¬ (C6611.det = 0 ∧ ∀ i, C6611.adjugate i i ≠ 0) := by
  intro h
  have := certificate6611
  rw [h.1] at this
  norm_num at this
def C6612 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6612 : C6612.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6612 : ¬ (C6612.det = 0 ∧ ∀ i, C6612.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6612
def C6613 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6613 : C6613.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6613 : ¬ (C6613.det = 0 ∧ ∀ i, C6613.adjugate i i ≠ 0) := by
  intro h
  have := certificate6613
  rw [h.1] at this
  norm_num at this
def C6614 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6614 : C6614.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6614 : ¬ (C6614.det = 0 ∧ ∀ i, C6614.adjugate i i ≠ 0) := by
  intro h
  have := certificate6614
  rw [h.1] at this
  norm_num at this
def C6615 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6615 : C6615.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6615 : ¬ (C6615.det = 0 ∧ ∀ i, C6615.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6615
def C6616 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6616 : C6616.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6616 : ¬ (C6616.det = 0 ∧ ∀ i, C6616.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6616
def C6617 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6617 : C6617.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6617 : ¬ (C6617.det = 0 ∧ ∀ i, C6617.adjugate i i ≠ 0) := by
  intro h
  have := certificate6617
  rw [h.1] at this
  norm_num at this
def C6618 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6618 : C6618.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6618 : ¬ (C6618.det = 0 ∧ ∀ i, C6618.adjugate i i ≠ 0) := by
  intro h
  have := certificate6618
  rw [h.1] at this
  norm_num at this
def C6619 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6619 : C6619.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6619 : ¬ (C6619.det = 0 ∧ ∀ i, C6619.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6619
def C6620 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6620 : C6620.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6620 : ¬ (C6620.det = 0 ∧ ∀ i, C6620.adjugate i i ≠ 0) := by
  intro h
  have := certificate6620
  rw [h.1] at this
  norm_num at this
def C6621 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6621 : C6621.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6621 : ¬ (C6621.det = 0 ∧ ∀ i, C6621.adjugate i i ≠ 0) := by
  intro h
  have := certificate6621
  rw [h.1] at this
  norm_num at this
def C6622 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6622 : C6622.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6622 : ¬ (C6622.det = 0 ∧ ∀ i, C6622.adjugate i i ≠ 0) := by
  intro h
  have := certificate6622
  rw [h.1] at this
  norm_num at this
def C6623 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6623 : C6623.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6623 : ¬ (C6623.det = 0 ∧ ∀ i, C6623.adjugate i i ≠ 0) := by
  intro h
  have := certificate6623
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0206
