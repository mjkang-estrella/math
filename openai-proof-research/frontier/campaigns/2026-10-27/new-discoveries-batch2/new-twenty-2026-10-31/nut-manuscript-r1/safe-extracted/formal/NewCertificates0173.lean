import VerifiedDet
namespace Nut8.NewCertificates0173
def C5536 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5536 : C5536.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5536 : ¬ (C5536.det = 0 ∧ ∀ i, C5536.adjugate i i ≠ 0) := by
  intro h
  have := certificate5536
  rw [h.1] at this
  norm_num at this
def C5537 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5537 : C5537.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5537 : ¬ (C5537.det = 0 ∧ ∀ i, C5537.adjugate i i ≠ 0) := by
  intro h
  have := certificate5537
  rw [h.1] at this
  norm_num at this
def C5538 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5538 : C5538.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5538 : ¬ (C5538.det = 0 ∧ ∀ i, C5538.adjugate i i ≠ 0) := by
  intro h
  have := certificate5538
  rw [h.1] at this
  norm_num at this
def C5539 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5539 : C5539.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5539 : ¬ (C5539.det = 0 ∧ ∀ i, C5539.adjugate i i ≠ 0) := by
  intro h
  have := certificate5539
  rw [h.1] at this
  norm_num at this
def C5540 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5540 : C5540.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5540 : ¬ (C5540.det = 0 ∧ ∀ i, C5540.adjugate i i ≠ 0) := by
  intro h
  have := certificate5540
  rw [h.1] at this
  norm_num at this
def C5541 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5541 : C5541.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5541 : ¬ (C5541.det = 0 ∧ ∀ i, C5541.adjugate i i ≠ 0) := by
  intro h
  have := certificate5541
  rw [h.1] at this
  norm_num at this
def C5542 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5542 : C5542.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5542 : ¬ (C5542.det = 0 ∧ ∀ i, C5542.adjugate i i ≠ 0) := by
  intro h
  have := certificate5542
  rw [h.1] at this
  norm_num at this
def C5543 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5543 : C5543.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5543 : ¬ (C5543.det = 0 ∧ ∀ i, C5543.adjugate i i ≠ 0) := by
  intro h
  have := certificate5543
  rw [h.1] at this
  norm_num at this
def C5544 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5544 : C5544.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5544 : ¬ (C5544.det = 0 ∧ ∀ i, C5544.adjugate i i ≠ 0) := by
  intro h
  have := certificate5544
  rw [h.1] at this
  norm_num at this
def C5545 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5545 : C5545.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5545 : ¬ (C5545.det = 0 ∧ ∀ i, C5545.adjugate i i ≠ 0) := by
  intro h
  have := certificate5545
  rw [h.1] at this
  norm_num at this
def C5546 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5546 : C5546.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5546 : ¬ (C5546.det = 0 ∧ ∀ i, C5546.adjugate i i ≠ 0) := by
  intro h
  have := certificate5546
  rw [h.1] at this
  norm_num at this
def C5547 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5547 : C5547.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5547 : ¬ (C5547.det = 0 ∧ ∀ i, C5547.adjugate i i ≠ 0) := by
  intro h
  have := certificate5547
  rw [h.1] at this
  norm_num at this
def C5548 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate5548 : C5548.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5548 : ¬ (C5548.det = 0 ∧ ∀ i, C5548.adjugate i i ≠ 0) := by
  intro h
  have := certificate5548
  rw [h.1] at this
  norm_num at this
def C5549 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate5549 : C5549.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5549 : ¬ (C5549.det = 0 ∧ ∀ i, C5549.adjugate i i ≠ 0) := by
  intro h
  have := certificate5549
  rw [h.1] at this
  norm_num at this
def C5550 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate5550 : C5550.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5550 : ¬ (C5550.det = 0 ∧ ∀ i, C5550.adjugate i i ≠ 0) := by
  intro h
  have := certificate5550
  rw [h.1] at this
  norm_num at this
def C5551 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate5551 : C5551.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5551 : ¬ (C5551.det = 0 ∧ ∀ i, C5551.adjugate i i ≠ 0) := by
  intro h
  have := certificate5551
  rw [h.1] at this
  norm_num at this
def C5552 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate5552 : C5552.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5552 : ¬ (C5552.det = 0 ∧ ∀ i, C5552.adjugate i i ≠ 0) := by
  intro h
  have := certificate5552
  rw [h.1] at this
  norm_num at this
def C5553 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate5553 : C5553.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5553 : ¬ (C5553.det = 0 ∧ ∀ i, C5553.adjugate i i ≠ 0) := by
  intro h
  have := certificate5553
  rw [h.1] at this
  norm_num at this
def C5554 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate5554 : C5554.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5554 : ¬ (C5554.det = 0 ∧ ∀ i, C5554.adjugate i i ≠ 0) := by
  intro h
  have := certificate5554
  rw [h.1] at this
  norm_num at this
def C5555 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate5555 : C5555.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5555 : ¬ (C5555.det = 0 ∧ ∀ i, C5555.adjugate i i ≠ 0) := by
  intro h
  have := certificate5555
  rw [h.1] at this
  norm_num at this
def C5556 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate5556 : C5556.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5556 : ¬ (C5556.det = 0 ∧ ∀ i, C5556.adjugate i i ≠ 0) := by
  intro h
  have := certificate5556
  rw [h.1] at this
  norm_num at this
def C5557 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate5557 : C5557.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5557 : ¬ (C5557.det = 0 ∧ ∀ i, C5557.adjugate i i ≠ 0) := by
  intro h
  have := certificate5557
  rw [h.1] at this
  norm_num at this
def C5558 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate5558 : C5558.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5558 : ¬ (C5558.det = 0 ∧ ∀ i, C5558.adjugate i i ≠ 0) := by
  intro h
  have := certificate5558
  rw [h.1] at this
  norm_num at this
def C5559 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate5559 : C5559.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5559 : ¬ (C5559.det = 0 ∧ ∀ i, C5559.adjugate i i ≠ 0) := by
  intro h
  have := certificate5559
  rw [h.1] at this
  norm_num at this
def C5560 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate5560 : C5560.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5560 : ¬ (C5560.det = 0 ∧ ∀ i, C5560.adjugate i i ≠ 0) := by
  intro h
  have := certificate5560
  rw [h.1] at this
  norm_num at this
def C5561 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate5561 : C5561.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5561 : ¬ (C5561.det = 0 ∧ ∀ i, C5561.adjugate i i ≠ 0) := by
  intro h
  have := certificate5561
  rw [h.1] at this
  norm_num at this
def C5562 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate5562 : C5562.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5562 : ¬ (C5562.det = 0 ∧ ∀ i, C5562.adjugate i i ≠ 0) := by
  intro h
  have := certificate5562
  rw [h.1] at this
  norm_num at this
def C5563 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate5563 : C5563.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5563 : ¬ (C5563.det = 0 ∧ ∀ i, C5563.adjugate i i ≠ 0) := by
  intro h
  have := certificate5563
  rw [h.1] at this
  norm_num at this
def C5564 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate5564 : C5564.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5564 : ¬ (C5564.det = 0 ∧ ∀ i, C5564.adjugate i i ≠ 0) := by
  intro h
  have := certificate5564
  rw [h.1] at this
  norm_num at this
def C5565 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate5565 : C5565.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5565 : ¬ (C5565.det = 0 ∧ ∀ i, C5565.adjugate i i ≠ 0) := by
  intro h
  have := certificate5565
  rw [h.1] at this
  norm_num at this
def C5566 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate5566 : C5566.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5566 : ¬ (C5566.det = 0 ∧ ∀ i, C5566.adjugate i i ≠ 0) := by
  intro h
  have := certificate5566
  rw [h.1] at this
  norm_num at this
def C5567 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate5567 : C5567.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5567 : ¬ (C5567.det = 0 ∧ ∀ i, C5567.adjugate i i ≠ 0) := by
  intro h
  have := certificate5567
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0173
