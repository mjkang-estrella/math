import VerifiedDet
namespace Nut8.NewCertificates0205
def C6560 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6560 : C6560.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6560 : ¬ (C6560.det = 0 ∧ ∀ i, C6560.adjugate i i ≠ 0) := by
  intro h
  have := certificate6560
  rw [h.1] at this
  norm_num at this
def C6561 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6561 : C6561.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6561 : ¬ (C6561.det = 0 ∧ ∀ i, C6561.adjugate i i ≠ 0) := by
  intro h
  have := certificate6561
  rw [h.1] at this
  norm_num at this
def C6562 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6562 : C6562.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6562 : ¬ (C6562.det = 0 ∧ ∀ i, C6562.adjugate i i ≠ 0) := by
  intro h
  have := certificate6562
  rw [h.1] at this
  norm_num at this
def C6563 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6563 : C6563.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6563 : ¬ (C6563.det = 0 ∧ ∀ i, C6563.adjugate i i ≠ 0) := by
  intro h
  have := certificate6563
  rw [h.1] at this
  norm_num at this
def C6564 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6564 : C6564.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6564 : ¬ (C6564.det = 0 ∧ ∀ i, C6564.adjugate i i ≠ 0) := by
  intro h
  have := certificate6564
  rw [h.1] at this
  norm_num at this
def C6565 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6565 : C6565.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6565 : ¬ (C6565.det = 0 ∧ ∀ i, C6565.adjugate i i ≠ 0) := by
  intro h
  have := certificate6565
  rw [h.1] at this
  norm_num at this
def C6566 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6566 : C6566.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6566 : ¬ (C6566.det = 0 ∧ ∀ i, C6566.adjugate i i ≠ 0) := by
  intro h
  have := certificate6566
  rw [h.1] at this
  norm_num at this
def C6567 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6567 : C6567.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6567 : ¬ (C6567.det = 0 ∧ ∀ i, C6567.adjugate i i ≠ 0) := by
  intro h
  have := certificate6567
  rw [h.1] at this
  norm_num at this
def C6568 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6568 : C6568.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6568 : ¬ (C6568.det = 0 ∧ ∀ i, C6568.adjugate i i ≠ 0) := by
  intro h
  have := certificate6568
  rw [h.1] at this
  norm_num at this
def C6569 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6569 : C6569.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6569 : ¬ (C6569.det = 0 ∧ ∀ i, C6569.adjugate i i ≠ 0) := by
  intro h
  have := certificate6569
  rw [h.1] at this
  norm_num at this
def C6570 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6570 : C6570.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6570 : ¬ (C6570.det = 0 ∧ ∀ i, C6570.adjugate i i ≠ 0) := by
  intro h
  have := certificate6570
  rw [h.1] at this
  norm_num at this
def C6571 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6571 : C6571.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6571 : ¬ (C6571.det = 0 ∧ ∀ i, C6571.adjugate i i ≠ 0) := by
  intro h
  have := certificate6571
  rw [h.1] at this
  norm_num at this
def C6572 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6572 : C6572.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6572 : ¬ (C6572.det = 0 ∧ ∀ i, C6572.adjugate i i ≠ 0) := by
  intro h
  have := certificate6572
  rw [h.1] at this
  norm_num at this
def C6573 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6573 : C6573.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6573 : ¬ (C6573.det = 0 ∧ ∀ i, C6573.adjugate i i ≠ 0) := by
  intro h
  have := certificate6573
  rw [h.1] at this
  norm_num at this
def C6574 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6574 : C6574.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6574 : ¬ (C6574.det = 0 ∧ ∀ i, C6574.adjugate i i ≠ 0) := by
  intro h
  have := certificate6574
  rw [h.1] at this
  norm_num at this
def C6575 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6575 : C6575.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6575 : ¬ (C6575.det = 0 ∧ ∀ i, C6575.adjugate i i ≠ 0) := by
  intro h
  have := certificate6575
  rw [h.1] at this
  norm_num at this
def C6576 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6576 : C6576.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6576 : ¬ (C6576.det = 0 ∧ ∀ i, C6576.adjugate i i ≠ 0) := by
  intro h
  have := certificate6576
  rw [h.1] at this
  norm_num at this
def C6577 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6577 : C6577.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6577 : ¬ (C6577.det = 0 ∧ ∀ i, C6577.adjugate i i ≠ 0) := by
  intro h
  have := certificate6577
  rw [h.1] at this
  norm_num at this
def C6578 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6578 : C6578.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6578 : ¬ (C6578.det = 0 ∧ ∀ i, C6578.adjugate i i ≠ 0) := by
  intro h
  have := certificate6578
  rw [h.1] at this
  norm_num at this
def C6579 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6579 : C6579.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6579 : ¬ (C6579.det = 0 ∧ ∀ i, C6579.adjugate i i ≠ 0) := by
  intro h
  have := certificate6579
  rw [h.1] at this
  norm_num at this
def C6580 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6580 : C6580.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6580 : ¬ (C6580.det = 0 ∧ ∀ i, C6580.adjugate i i ≠ 0) := by
  intro h
  have := certificate6580
  rw [h.1] at this
  norm_num at this
def C6581 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6581 : C6581.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6581 : ¬ (C6581.det = 0 ∧ ∀ i, C6581.adjugate i i ≠ 0) := by
  intro h
  have := certificate6581
  rw [h.1] at this
  norm_num at this
def C6582 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6582 : C6582.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6582 : ¬ (C6582.det = 0 ∧ ∀ i, C6582.adjugate i i ≠ 0) := by
  intro h
  have := certificate6582
  rw [h.1] at this
  norm_num at this
def C6583 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6583 : C6583.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6583 : ¬ (C6583.det = 0 ∧ ∀ i, C6583.adjugate i i ≠ 0) := by
  intro h
  have := certificate6583
  rw [h.1] at this
  norm_num at this
def C6584 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6584 : C6584.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6584 : ¬ (C6584.det = 0 ∧ ∀ i, C6584.adjugate i i ≠ 0) := by
  intro h
  have := certificate6584
  rw [h.1] at this
  norm_num at this
def C6585 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6585 : C6585.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6585 : ¬ (C6585.det = 0 ∧ ∀ i, C6585.adjugate i i ≠ 0) := by
  intro h
  have := certificate6585
  rw [h.1] at this
  norm_num at this
def C6586 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6586 : C6586.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6586 : ¬ (C6586.det = 0 ∧ ∀ i, C6586.adjugate i i ≠ 0) := by
  intro h
  have := certificate6586
  rw [h.1] at this
  norm_num at this
def C6587 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6587 : C6587.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6587 : ¬ (C6587.det = 0 ∧ ∀ i, C6587.adjugate i i ≠ 0) := by
  intro h
  have := certificate6587
  rw [h.1] at this
  norm_num at this
def C6588 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6588 : C6588.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6588 : ¬ (C6588.det = 0 ∧ ∀ i, C6588.adjugate i i ≠ 0) := by
  intro h
  have := certificate6588
  rw [h.1] at this
  norm_num at this
def C6589 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6589 : C6589.det = (-45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6589 : ¬ (C6589.det = 0 ∧ ∀ i, C6589.adjugate i i ≠ 0) := by
  intro h
  have := certificate6589
  rw [h.1] at this
  norm_num at this
def C6590 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6590 : C6590.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6590 : ¬ (C6590.det = 0 ∧ ∀ i, C6590.adjugate i i ≠ 0) := by
  intro h
  have := certificate6590
  rw [h.1] at this
  norm_num at this
def C6591 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6591 : C6591.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6591 : ¬ (C6591.det = 0 ∧ ∀ i, C6591.adjugate i i ≠ 0) := by
  intro h
  have := certificate6591
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0205
