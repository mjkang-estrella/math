import VerifiedDet
namespace Nut8.NewCertificates0142
def C4544 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4544 : C4544.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4544 : ¬ (C4544.det = 0 ∧ ∀ i, C4544.adjugate i i ≠ 0) := by
  intro h
  have := certificate4544
  rw [h.1] at this
  norm_num at this
def C4545 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4545 : C4545.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4545 : ¬ (C4545.det = 0 ∧ ∀ i, C4545.adjugate i i ≠ 0) := by
  intro h
  have := certificate4545
  rw [h.1] at this
  norm_num at this
def C4546 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4546 : C4546.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4546 : ¬ (C4546.det = 0 ∧ ∀ i, C4546.adjugate i i ≠ 0) := by
  intro h
  have := certificate4546
  rw [h.1] at this
  norm_num at this
def C4547 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4547 : C4547.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4547 : ¬ (C4547.det = 0 ∧ ∀ i, C4547.adjugate i i ≠ 0) := by
  intro h
  have := certificate4547
  rw [h.1] at this
  norm_num at this
def C4548 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4548 : C4548.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4548 : ¬ (C4548.det = 0 ∧ ∀ i, C4548.adjugate i i ≠ 0) := by
  intro h
  have := certificate4548
  rw [h.1] at this
  norm_num at this
def C4549 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4549 : C4549.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4549 : ¬ (C4549.det = 0 ∧ ∀ i, C4549.adjugate i i ≠ 0) := by
  intro h
  have := certificate4549
  rw [h.1] at this
  norm_num at this
def C4550 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4550 : C4550.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4550 : ¬ (C4550.det = 0 ∧ ∀ i, C4550.adjugate i i ≠ 0) := by
  intro h
  have := certificate4550
  rw [h.1] at this
  norm_num at this
def C4551 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4551 : C4551.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4551 : ¬ (C4551.det = 0 ∧ ∀ i, C4551.adjugate i i ≠ 0) := by
  intro h
  have := certificate4551
  rw [h.1] at this
  norm_num at this
def C4552 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4552 : C4552.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4552 : ¬ (C4552.det = 0 ∧ ∀ i, C4552.adjugate i i ≠ 0) := by
  intro h
  have := certificate4552
  rw [h.1] at this
  norm_num at this
def C4553 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4553 : C4553.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4553 : ¬ (C4553.det = 0 ∧ ∀ i, C4553.adjugate i i ≠ 0) := by
  intro h
  have := certificate4553
  rw [h.1] at this
  norm_num at this
def C4554 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4554 : C4554.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4554 : ¬ (C4554.det = 0 ∧ ∀ i, C4554.adjugate i i ≠ 0) := by
  intro h
  have := certificate4554
  rw [h.1] at this
  norm_num at this
def C4555 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4555 : C4555.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4555 : ¬ (C4555.det = 0 ∧ ∀ i, C4555.adjugate i i ≠ 0) := by
  intro h
  have := certificate4555
  rw [h.1] at this
  norm_num at this
def C4556 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4556 : C4556.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4556 : ¬ (C4556.det = 0 ∧ ∀ i, C4556.adjugate i i ≠ 0) := by
  intro h
  have := certificate4556
  rw [h.1] at this
  norm_num at this
def C4557 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4557 : C4557.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4557 : ¬ (C4557.det = 0 ∧ ∀ i, C4557.adjugate i i ≠ 0) := by
  intro h
  have := certificate4557
  rw [h.1] at this
  norm_num at this
def C4558 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4558 : C4558.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4558 : ¬ (C4558.det = 0 ∧ ∀ i, C4558.adjugate i i ≠ 0) := by
  intro h
  have := certificate4558
  rw [h.1] at this
  norm_num at this
def C4559 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4559 : C4559.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4559 : ¬ (C4559.det = 0 ∧ ∀ i, C4559.adjugate i i ≠ 0) := by
  intro h
  have := certificate4559
  rw [h.1] at this
  norm_num at this
def C4560 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4560 : C4560.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4560 : ¬ (C4560.det = 0 ∧ ∀ i, C4560.adjugate i i ≠ 0) := by
  intro h
  have := certificate4560
  rw [h.1] at this
  norm_num at this
def C4561 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4561 : C4561.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4561 : ¬ (C4561.det = 0 ∧ ∀ i, C4561.adjugate i i ≠ 0) := by
  intro h
  have := certificate4561
  rw [h.1] at this
  norm_num at this
def C4562 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4562 : C4562.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4562 : ¬ (C4562.det = 0 ∧ ∀ i, C4562.adjugate i i ≠ 0) := by
  intro h
  have := certificate4562
  rw [h.1] at this
  norm_num at this
def C4563 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4563 : C4563.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4563 : ¬ (C4563.det = 0 ∧ ∀ i, C4563.adjugate i i ≠ 0) := by
  intro h
  have := certificate4563
  rw [h.1] at this
  norm_num at this
def C4564 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4564 : C4564.det = (53 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4564 : ¬ (C4564.det = 0 ∧ ∀ i, C4564.adjugate i i ≠ 0) := by
  intro h
  have := certificate4564
  rw [h.1] at this
  norm_num at this
def C4565 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4565 : C4565.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4565 : ¬ (C4565.det = 0 ∧ ∀ i, C4565.adjugate i i ≠ 0) := by
  intro h
  have := certificate4565
  rw [h.1] at this
  norm_num at this
def C4566 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4566 : C4566.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4566 : ¬ (C4566.det = 0 ∧ ∀ i, C4566.adjugate i i ≠ 0) := by
  intro h
  have := certificate4566
  rw [h.1] at this
  norm_num at this
def C4567 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4567 : C4567.det = (53 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4567 : ¬ (C4567.det = 0 ∧ ∀ i, C4567.adjugate i i ≠ 0) := by
  intro h
  have := certificate4567
  rw [h.1] at this
  norm_num at this
def C4568 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4568 : C4568.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4568 : ¬ (C4568.det = 0 ∧ ∀ i, C4568.adjugate i i ≠ 0) := by
  intro h
  have := certificate4568
  rw [h.1] at this
  norm_num at this
def C4569 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4569 : C4569.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4569 : ¬ (C4569.det = 0 ∧ ∀ i, C4569.adjugate i i ≠ 0) := by
  intro h
  have := certificate4569
  rw [h.1] at this
  norm_num at this
def C4570 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4570 : C4570.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4570 : ¬ (C4570.det = 0 ∧ ∀ i, C4570.adjugate i i ≠ 0) := by
  intro h
  have := certificate4570
  rw [h.1] at this
  norm_num at this
def C4571 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate4571 : C4571.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4571 : ¬ (C4571.det = 0 ∧ ∀ i, C4571.adjugate i i ≠ 0) := by
  intro h
  have := certificate4571
  rw [h.1] at this
  norm_num at this
def C4572 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4572 : C4572.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4572 : ¬ (C4572.det = 0 ∧ ∀ i, C4572.adjugate i i ≠ 0) := by
  intro h
  have := certificate4572
  rw [h.1] at this
  norm_num at this
def C4573 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate4573 : C4573.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4573 : ¬ (C4573.det = 0 ∧ ∀ i, C4573.adjugate i i ≠ 0) := by
  intro h
  have := certificate4573
  rw [h.1] at this
  norm_num at this
def C4574 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate4574 : C4574.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4574 : ¬ (C4574.det = 0 ∧ ∀ i, C4574.adjugate i i ≠ 0) := by
  intro h
  have := certificate4574
  rw [h.1] at this
  norm_num at this
def C4575 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate4575 : C4575.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4575 : ¬ (C4575.det = 0 ∧ ∀ i, C4575.adjugate i i ≠ 0) := by
  intro h
  have := certificate4575
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0142
