import VerifiedDet
namespace Nut8.NewCertificates0269
def C8608 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8608 : C8608.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8608 : ¬ (C8608.det = 0 ∧ ∀ i, C8608.adjugate i i ≠ 0) := by
  intro h
  have := certificate8608
  rw [h.1] at this
  norm_num at this
def C8609 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8609 : C8609.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8609 : ¬ (C8609.det = 0 ∧ ∀ i, C8609.adjugate i i ≠ 0) := by
  intro h
  have := certificate8609
  rw [h.1] at this
  norm_num at this
def C8610 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8610 : C8610.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8610 : ¬ (C8610.det = 0 ∧ ∀ i, C8610.adjugate i i ≠ 0) := by
  intro h
  have := certificate8610
  rw [h.1] at this
  norm_num at this
def C8611 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8611 : C8611.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8611 : ¬ (C8611.det = 0 ∧ ∀ i, C8611.adjugate i i ≠ 0) := by
  intro h
  have := certificate8611
  rw [h.1] at this
  norm_num at this
def C8612 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8612 : C8612.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8612 : ¬ (C8612.det = 0 ∧ ∀ i, C8612.adjugate i i ≠ 0) := by
  intro h
  have := certificate8612
  rw [h.1] at this
  norm_num at this
def C8613 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8613 : C8613.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8613 : ¬ (C8613.det = 0 ∧ ∀ i, C8613.adjugate i i ≠ 0) := by
  intro h
  have := certificate8613
  rw [h.1] at this
  norm_num at this
def C8614 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8614 : C8614.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8614 : ¬ (C8614.det = 0 ∧ ∀ i, C8614.adjugate i i ≠ 0) := by
  intro h
  have := certificate8614
  rw [h.1] at this
  norm_num at this
def C8615 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8615 : C8615.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8615 : ¬ (C8615.det = 0 ∧ ∀ i, C8615.adjugate i i ≠ 0) := by
  intro h
  have := certificate8615
  rw [h.1] at this
  norm_num at this
def C8616 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8616 : C8616.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8616 : ¬ (C8616.det = 0 ∧ ∀ i, C8616.adjugate i i ≠ 0) := by
  intro h
  have := certificate8616
  rw [h.1] at this
  norm_num at this
def C8617 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8617 : C8617.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8617 : ¬ (C8617.det = 0 ∧ ∀ i, C8617.adjugate i i ≠ 0) := by
  intro h
  have := certificate8617
  rw [h.1] at this
  norm_num at this
def C8618 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8618 : C8618.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8618 : ¬ (C8618.det = 0 ∧ ∀ i, C8618.adjugate i i ≠ 0) := by
  intro h
  have := certificate8618
  rw [h.1] at this
  norm_num at this
def C8619 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8619 : C8619.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8619 : ¬ (C8619.det = 0 ∧ ∀ i, C8619.adjugate i i ≠ 0) := by
  intro h
  have := certificate8619
  rw [h.1] at this
  norm_num at this
def C8620 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8620 : C8620.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8620 : ¬ (C8620.det = 0 ∧ ∀ i, C8620.adjugate i i ≠ 0) := by
  intro h
  have := certificate8620
  rw [h.1] at this
  norm_num at this
def C8621 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8621 : C8621.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8621 : ¬ (C8621.det = 0 ∧ ∀ i, C8621.adjugate i i ≠ 0) := by
  intro h
  have := certificate8621
  rw [h.1] at this
  norm_num at this
def C8622 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8622 : C8622.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8622 : ¬ (C8622.det = 0 ∧ ∀ i, C8622.adjugate i i ≠ 0) := by
  intro h
  have := certificate8622
  rw [h.1] at this
  norm_num at this
def C8623 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8623 : C8623.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8623 : ¬ (C8623.det = 0 ∧ ∀ i, C8623.adjugate i i ≠ 0) := by
  intro h
  have := certificate8623
  rw [h.1] at this
  norm_num at this
def C8624 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8624 : C8624.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8624 : ¬ (C8624.det = 0 ∧ ∀ i, C8624.adjugate i i ≠ 0) := by
  intro h
  have := certificate8624
  rw [h.1] at this
  norm_num at this
def C8625 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8625 : C8625.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8625 : ¬ (C8625.det = 0 ∧ ∀ i, C8625.adjugate i i ≠ 0) := by
  intro h
  have := certificate8625
  rw [h.1] at this
  norm_num at this
def C8626 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8626 : C8626.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8626 : ¬ (C8626.det = 0 ∧ ∀ i, C8626.adjugate i i ≠ 0) := by
  intro h
  have := certificate8626
  rw [h.1] at this
  norm_num at this
def C8627 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8627 : C8627.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8627 : ¬ (C8627.det = 0 ∧ ∀ i, C8627.adjugate i i ≠ 0) := by
  intro h
  have := certificate8627
  rw [h.1] at this
  norm_num at this
def C8628 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8628 : C8628.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8628 : ¬ (C8628.det = 0 ∧ ∀ i, C8628.adjugate i i ≠ 0) := by
  intro h
  have := certificate8628
  rw [h.1] at this
  norm_num at this
def C8629 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8629 : C8629.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8629 : ¬ (C8629.det = 0 ∧ ∀ i, C8629.adjugate i i ≠ 0) := by
  intro h
  have := certificate8629
  rw [h.1] at this
  norm_num at this
def C8630 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8630 : C8630.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8630 : ¬ (C8630.det = 0 ∧ ∀ i, C8630.adjugate i i ≠ 0) := by
  intro h
  have := certificate8630
  rw [h.1] at this
  norm_num at this
def C8631 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8631 : C8631.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8631 : ¬ (C8631.det = 0 ∧ ∀ i, C8631.adjugate i i ≠ 0) := by
  intro h
  have := certificate8631
  rw [h.1] at this
  norm_num at this
def C8632 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8632 : C8632.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8632 : ¬ (C8632.det = 0 ∧ ∀ i, C8632.adjugate i i ≠ 0) := by
  intro h
  have := certificate8632
  rw [h.1] at this
  norm_num at this
def C8633 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8633 : C8633.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8633 : ¬ (C8633.det = 0 ∧ ∀ i, C8633.adjugate i i ≠ 0) := by
  intro h
  have := certificate8633
  rw [h.1] at this
  norm_num at this
def C8634 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8634 : C8634.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8634 : ¬ (C8634.det = 0 ∧ ∀ i, C8634.adjugate i i ≠ 0) := by
  intro h
  have := certificate8634
  rw [h.1] at this
  norm_num at this
def C8635 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8635 : C8635.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8635 : ¬ (C8635.det = 0 ∧ ∀ i, C8635.adjugate i i ≠ 0) := by
  intro h
  have := certificate8635
  rw [h.1] at this
  norm_num at this
def C8636 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8636 : C8636.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8636 : ¬ (C8636.det = 0 ∧ ∀ i, C8636.adjugate i i ≠ 0) := by
  intro h
  have := certificate8636
  rw [h.1] at this
  norm_num at this
def C8637 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8637 : C8637.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8637 : ¬ (C8637.det = 0 ∧ ∀ i, C8637.adjugate i i ≠ 0) := by
  intro h
  have := certificate8637
  rw [h.1] at this
  norm_num at this
def C8638 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8638 : C8638.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8638 : ¬ (C8638.det = 0 ∧ ∀ i, C8638.adjugate i i ≠ 0) := by
  intro h
  have := certificate8638
  rw [h.1] at this
  norm_num at this
def C8639 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8639 : C8639.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8639 : ¬ (C8639.det = 0 ∧ ∀ i, C8639.adjugate i i ≠ 0) := by
  intro h
  have := certificate8639
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0269
