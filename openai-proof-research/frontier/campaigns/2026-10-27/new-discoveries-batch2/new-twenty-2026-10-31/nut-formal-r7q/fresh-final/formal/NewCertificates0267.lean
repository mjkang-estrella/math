import VerifiedDet
namespace Nut8.NewCertificates0267
def C8544 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8544 : C8544.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8544 : ¬ (C8544.det = 0 ∧ ∀ i, C8544.adjugate i i ≠ 0) := by
  intro h
  have := certificate8544
  rw [h.1] at this
  norm_num at this
def C8545 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8545 : C8545.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8545 : ¬ (C8545.det = 0 ∧ ∀ i, C8545.adjugate i i ≠ 0) := by
  intro h
  have := certificate8545
  rw [h.1] at this
  norm_num at this
def C8546 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8546 : C8546.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8546 : ¬ (C8546.det = 0 ∧ ∀ i, C8546.adjugate i i ≠ 0) := by
  intro h
  have := certificate8546
  rw [h.1] at this
  norm_num at this
def C8547 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8547 : C8547.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8547 : ¬ (C8547.det = 0 ∧ ∀ i, C8547.adjugate i i ≠ 0) := by
  intro h
  have := certificate8547
  rw [h.1] at this
  norm_num at this
def C8548 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8548 : C8548.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8548 : ¬ (C8548.det = 0 ∧ ∀ i, C8548.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8548
def C8549 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8549 : C8549.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8549 : ¬ (C8549.det = 0 ∧ ∀ i, C8549.adjugate i i ≠ 0) := by
  intro h
  have := certificate8549
  rw [h.1] at this
  norm_num at this
def C8550 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8550 : C8550.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8550 : ¬ (C8550.det = 0 ∧ ∀ i, C8550.adjugate i i ≠ 0) := by
  intro h
  have := certificate8550
  rw [h.1] at this
  norm_num at this
def C8551 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8551 : C8551.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8551 : ¬ (C8551.det = 0 ∧ ∀ i, C8551.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8551
def C8552 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8552 : C8552.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8552 : ¬ (C8552.det = 0 ∧ ∀ i, C8552.adjugate i i ≠ 0) := by
  intro h
  have := certificate8552
  rw [h.1] at this
  norm_num at this
def C8553 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8553 : C8553.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8553 : ¬ (C8553.det = 0 ∧ ∀ i, C8553.adjugate i i ≠ 0) := by
  intro h
  have := certificate8553
  rw [h.1] at this
  norm_num at this
def C8554 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8554 : C8554.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8554 : ¬ (C8554.det = 0 ∧ ∀ i, C8554.adjugate i i ≠ 0) := by
  intro h
  have := certificate8554
  rw [h.1] at this
  norm_num at this
def C8555 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8555 : C8555.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8555 : ¬ (C8555.det = 0 ∧ ∀ i, C8555.adjugate i i ≠ 0) := by
  intro h
  have := certificate8555
  rw [h.1] at this
  norm_num at this
def C8556 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8556 : C8556.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8556 : ¬ (C8556.det = 0 ∧ ∀ i, C8556.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8556
def C8557 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8557 : C8557.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8557 : ¬ (C8557.det = 0 ∧ ∀ i, C8557.adjugate i i ≠ 0) := by
  intro h
  have := certificate8557
  rw [h.1] at this
  norm_num at this
def C8558 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8558 : C8558.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8558 : ¬ (C8558.det = 0 ∧ ∀ i, C8558.adjugate i i ≠ 0) := by
  intro h
  have := certificate8558
  rw [h.1] at this
  norm_num at this
def C8559 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8559 : C8559.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8559 : ¬ (C8559.det = 0 ∧ ∀ i, C8559.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8559
def C8560 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8560 : C8560.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8560 : ¬ (C8560.det = 0 ∧ ∀ i, C8560.adjugate i i ≠ 0) := by
  intro h
  have := certificate8560
  rw [h.1] at this
  norm_num at this
def C8561 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8561 : C8561.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8561 : ¬ (C8561.det = 0 ∧ ∀ i, C8561.adjugate i i ≠ 0) := by
  intro h
  have := certificate8561
  rw [h.1] at this
  norm_num at this
def C8562 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8562 : C8562.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8562 : ¬ (C8562.det = 0 ∧ ∀ i, C8562.adjugate i i ≠ 0) := by
  intro h
  have := certificate8562
  rw [h.1] at this
  norm_num at this
def C8563 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8563 : C8563.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8563 : ¬ (C8563.det = 0 ∧ ∀ i, C8563.adjugate i i ≠ 0) := by
  intro h
  have := certificate8563
  rw [h.1] at this
  norm_num at this
def C8564 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8564 : C8564.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8564 : ¬ (C8564.det = 0 ∧ ∀ i, C8564.adjugate i i ≠ 0) := by
  intro h
  have := certificate8564
  rw [h.1] at this
  norm_num at this
def C8565 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8565 : C8565.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8565 : ¬ (C8565.det = 0 ∧ ∀ i, C8565.adjugate i i ≠ 0) := by
  intro h
  have := certificate8565
  rw [h.1] at this
  norm_num at this
def C8566 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8566 : C8566.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8566 : ¬ (C8566.det = 0 ∧ ∀ i, C8566.adjugate i i ≠ 0) := by
  intro h
  have := certificate8566
  rw [h.1] at this
  norm_num at this
def C8567 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8567 : C8567.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8567 : ¬ (C8567.det = 0 ∧ ∀ i, C8567.adjugate i i ≠ 0) := by
  intro h
  have := certificate8567
  rw [h.1] at this
  norm_num at this
def C8568 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8568 : C8568.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8568 : ¬ (C8568.det = 0 ∧ ∀ i, C8568.adjugate i i ≠ 0) := by
  intro h
  have := certificate8568
  rw [h.1] at this
  norm_num at this
def C8569 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8569 : C8569.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8569 : ¬ (C8569.det = 0 ∧ ∀ i, C8569.adjugate i i ≠ 0) := by
  intro h
  have := certificate8569
  rw [h.1] at this
  norm_num at this
def C8570 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8570 : C8570.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8570 : ¬ (C8570.det = 0 ∧ ∀ i, C8570.adjugate i i ≠ 0) := by
  intro h
  have := certificate8570
  rw [h.1] at this
  norm_num at this
def C8571 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8571 : C8571.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8571 : ¬ (C8571.det = 0 ∧ ∀ i, C8571.adjugate i i ≠ 0) := by
  intro h
  have := certificate8571
  rw [h.1] at this
  norm_num at this
def C8572 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8572 : C8572.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8572 : ¬ (C8572.det = 0 ∧ ∀ i, C8572.adjugate i i ≠ 0) := by
  intro h
  have := certificate8572
  rw [h.1] at this
  norm_num at this
def C8573 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8573 : C8573.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8573 : ¬ (C8573.det = 0 ∧ ∀ i, C8573.adjugate i i ≠ 0) := by
  intro h
  have := certificate8573
  rw [h.1] at this
  norm_num at this
def C8574 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8574 : C8574.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8574 : ¬ (C8574.det = 0 ∧ ∀ i, C8574.adjugate i i ≠ 0) := by
  intro h
  have := certificate8574
  rw [h.1] at this
  norm_num at this
def C8575 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8575 : C8575.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8575 : ¬ (C8575.det = 0 ∧ ∀ i, C8575.adjugate i i ≠ 0) := by
  intro h
  have := certificate8575
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0267
