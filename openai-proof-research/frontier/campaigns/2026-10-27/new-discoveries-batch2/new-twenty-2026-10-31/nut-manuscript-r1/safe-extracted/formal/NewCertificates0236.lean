import VerifiedDet
namespace Nut8.NewCertificates0236
def C7552 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7552 : C7552.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7552 : ¬ (C7552.det = 0 ∧ ∀ i, C7552.adjugate i i ≠ 0) := by
  intro h
  have := certificate7552
  rw [h.1] at this
  norm_num at this
def C7553 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7553 : C7553.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7553 : ¬ (C7553.det = 0 ∧ ∀ i, C7553.adjugate i i ≠ 0) := by
  intro h
  have := certificate7553
  rw [h.1] at this
  norm_num at this
def C7554 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7554 : C7554.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7554 : ¬ (C7554.det = 0 ∧ ∀ i, C7554.adjugate i i ≠ 0) := by
  intro h
  have := certificate7554
  rw [h.1] at this
  norm_num at this
def C7555 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7555 : C7555.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7555 : ¬ (C7555.det = 0 ∧ ∀ i, C7555.adjugate i i ≠ 0) := by
  intro h
  have := certificate7555
  rw [h.1] at this
  norm_num at this
def C7556 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7556 : C7556.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7556 : ¬ (C7556.det = 0 ∧ ∀ i, C7556.adjugate i i ≠ 0) := by
  intro h
  have := certificate7556
  rw [h.1] at this
  norm_num at this
def C7557 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7557 : C7557.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7557 : ¬ (C7557.det = 0 ∧ ∀ i, C7557.adjugate i i ≠ 0) := by
  intro h
  have := certificate7557
  rw [h.1] at this
  norm_num at this
def C7558 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7558 : C7558.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7558 : ¬ (C7558.det = 0 ∧ ∀ i, C7558.adjugate i i ≠ 0) := by
  intro h
  have := certificate7558
  rw [h.1] at this
  norm_num at this
def C7559 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7559 : C7559.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7559 : ¬ (C7559.det = 0 ∧ ∀ i, C7559.adjugate i i ≠ 0) := by
  intro h
  have := certificate7559
  rw [h.1] at this
  norm_num at this
def C7560 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7560 : C7560.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7560 : ¬ (C7560.det = 0 ∧ ∀ i, C7560.adjugate i i ≠ 0) := by
  intro h
  have := certificate7560
  rw [h.1] at this
  norm_num at this
def C7561 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7561 : C7561.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7561 : ¬ (C7561.det = 0 ∧ ∀ i, C7561.adjugate i i ≠ 0) := by
  intro h
  have := certificate7561
  rw [h.1] at this
  norm_num at this
def C7562 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7562 : C7562.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7562 : ¬ (C7562.det = 0 ∧ ∀ i, C7562.adjugate i i ≠ 0) := by
  intro h
  have := certificate7562
  rw [h.1] at this
  norm_num at this
def C7563 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7563 : C7563.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7563 : ¬ (C7563.det = 0 ∧ ∀ i, C7563.adjugate i i ≠ 0) := by
  intro h
  have := certificate7563
  rw [h.1] at this
  norm_num at this
def C7564 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7564 : C7564.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7564 : ¬ (C7564.det = 0 ∧ ∀ i, C7564.adjugate i i ≠ 0) := by
  intro h
  have := certificate7564
  rw [h.1] at this
  norm_num at this
def C7565 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7565 : C7565.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7565 : ¬ (C7565.det = 0 ∧ ∀ i, C7565.adjugate i i ≠ 0) := by
  intro h
  have := certificate7565
  rw [h.1] at this
  norm_num at this
def C7566 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7566 : C7566.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7566 : ¬ (C7566.det = 0 ∧ ∀ i, C7566.adjugate i i ≠ 0) := by
  intro h
  have := certificate7566
  rw [h.1] at this
  norm_num at this
def C7567 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7567 : C7567.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7567 : ¬ (C7567.det = 0 ∧ ∀ i, C7567.adjugate i i ≠ 0) := by
  intro h
  have := certificate7567
  rw [h.1] at this
  norm_num at this
def C7568 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7568 : C7568.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7568 : ¬ (C7568.det = 0 ∧ ∀ i, C7568.adjugate i i ≠ 0) := by
  intro h
  have := certificate7568
  rw [h.1] at this
  norm_num at this
def C7569 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7569 : C7569.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7569 : ¬ (C7569.det = 0 ∧ ∀ i, C7569.adjugate i i ≠ 0) := by
  intro h
  have := certificate7569
  rw [h.1] at this
  norm_num at this
def C7570 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7570 : C7570.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7570 : ¬ (C7570.det = 0 ∧ ∀ i, C7570.adjugate i i ≠ 0) := by
  intro h
  have := certificate7570
  rw [h.1] at this
  norm_num at this
def C7571 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7571 : C7571.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7571 : ¬ (C7571.det = 0 ∧ ∀ i, C7571.adjugate i i ≠ 0) := by
  intro h
  have := certificate7571
  rw [h.1] at this
  norm_num at this
def C7572 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7572 : C7572.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7572 : ¬ (C7572.det = 0 ∧ ∀ i, C7572.adjugate i i ≠ 0) := by
  intro h
  have := certificate7572
  rw [h.1] at this
  norm_num at this
def C7573 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7573 : C7573.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7573 : ¬ (C7573.det = 0 ∧ ∀ i, C7573.adjugate i i ≠ 0) := by
  intro h
  have := certificate7573
  rw [h.1] at this
  norm_num at this
def C7574 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7574 : C7574.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7574 : ¬ (C7574.det = 0 ∧ ∀ i, C7574.adjugate i i ≠ 0) := by
  intro h
  have := certificate7574
  rw [h.1] at this
  norm_num at this
def C7575 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7575 : C7575.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7575 : ¬ (C7575.det = 0 ∧ ∀ i, C7575.adjugate i i ≠ 0) := by
  intro h
  have := certificate7575
  rw [h.1] at this
  norm_num at this
def C7576 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7576 : C7576.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7576 : ¬ (C7576.det = 0 ∧ ∀ i, C7576.adjugate i i ≠ 0) := by
  intro h
  have := certificate7576
  rw [h.1] at this
  norm_num at this
def C7577 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7577 : C7577.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7577 : ¬ (C7577.det = 0 ∧ ∀ i, C7577.adjugate i i ≠ 0) := by
  intro h
  have := certificate7577
  rw [h.1] at this
  norm_num at this
def C7578 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7578 : C7578.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7578 : ¬ (C7578.det = 0 ∧ ∀ i, C7578.adjugate i i ≠ 0) := by
  intro h
  have := certificate7578
  rw [h.1] at this
  norm_num at this
def C7579 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7579 : C7579.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7579 : ¬ (C7579.det = 0 ∧ ∀ i, C7579.adjugate i i ≠ 0) := by
  intro h
  have := certificate7579
  rw [h.1] at this
  norm_num at this
def C7580 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7580 : C7580.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7580 : ¬ (C7580.det = 0 ∧ ∀ i, C7580.adjugate i i ≠ 0) := by
  intro h
  have := certificate7580
  rw [h.1] at this
  norm_num at this
def C7581 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7581 : C7581.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7581 : ¬ (C7581.det = 0 ∧ ∀ i, C7581.adjugate i i ≠ 0) := by
  intro h
  have := certificate7581
  rw [h.1] at this
  norm_num at this
def C7582 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7582 : C7582.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7582 : ¬ (C7582.det = 0 ∧ ∀ i, C7582.adjugate i i ≠ 0) := by
  intro h
  have := certificate7582
  rw [h.1] at this
  norm_num at this
def C7583 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7583 : C7583.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7583 : ¬ (C7583.det = 0 ∧ ∀ i, C7583.adjugate i i ≠ 0) := by
  intro h
  have := certificate7583
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0236
