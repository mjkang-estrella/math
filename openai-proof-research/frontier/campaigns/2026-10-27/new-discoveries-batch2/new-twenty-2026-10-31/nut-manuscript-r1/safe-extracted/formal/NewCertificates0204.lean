import VerifiedDet
namespace Nut8.NewCertificates0204
def C6528 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6528 : C6528.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6528 : ¬ (C6528.det = 0 ∧ ∀ i, C6528.adjugate i i ≠ 0) := by
  intro h
  have := certificate6528
  rw [h.1] at this
  norm_num at this
def C6529 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6529 : C6529.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6529 : ¬ (C6529.det = 0 ∧ ∀ i, C6529.adjugate i i ≠ 0) := by
  intro h
  have := certificate6529
  rw [h.1] at this
  norm_num at this
def C6530 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6530 : C6530.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6530 : ¬ (C6530.det = 0 ∧ ∀ i, C6530.adjugate i i ≠ 0) := by
  intro h
  have := certificate6530
  rw [h.1] at this
  norm_num at this
def C6531 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6531 : C6531.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6531 : ¬ (C6531.det = 0 ∧ ∀ i, C6531.adjugate i i ≠ 0) := by
  intro h
  have := certificate6531
  rw [h.1] at this
  norm_num at this
def C6532 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6532 : C6532.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6532 : ¬ (C6532.det = 0 ∧ ∀ i, C6532.adjugate i i ≠ 0) := by
  intro h
  have := certificate6532
  rw [h.1] at this
  norm_num at this
def C6533 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6533 : C6533.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6533 : ¬ (C6533.det = 0 ∧ ∀ i, C6533.adjugate i i ≠ 0) := by
  intro h
  have := certificate6533
  rw [h.1] at this
  norm_num at this
def C6534 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6534 : C6534.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6534 : ¬ (C6534.det = 0 ∧ ∀ i, C6534.adjugate i i ≠ 0) := by
  intro h
  have := certificate6534
  rw [h.1] at this
  norm_num at this
def C6535 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6535 : C6535.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6535 : ¬ (C6535.det = 0 ∧ ∀ i, C6535.adjugate i i ≠ 0) := by
  intro h
  have := certificate6535
  rw [h.1] at this
  norm_num at this
def C6536 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6536 : C6536.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6536 : ¬ (C6536.det = 0 ∧ ∀ i, C6536.adjugate i i ≠ 0) := by
  intro h
  have := certificate6536
  rw [h.1] at this
  norm_num at this
def C6537 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6537 : C6537.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6537 : ¬ (C6537.det = 0 ∧ ∀ i, C6537.adjugate i i ≠ 0) := by
  intro h
  have := certificate6537
  rw [h.1] at this
  norm_num at this
def C6538 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6538 : C6538.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6538 : ¬ (C6538.det = 0 ∧ ∀ i, C6538.adjugate i i ≠ 0) := by
  intro h
  have := certificate6538
  rw [h.1] at this
  norm_num at this
def C6539 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6539 : C6539.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6539 : ¬ (C6539.det = 0 ∧ ∀ i, C6539.adjugate i i ≠ 0) := by
  intro h
  have := certificate6539
  rw [h.1] at this
  norm_num at this
def C6540 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6540 : C6540.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6540 : ¬ (C6540.det = 0 ∧ ∀ i, C6540.adjugate i i ≠ 0) := by
  intro h
  have := certificate6540
  rw [h.1] at this
  norm_num at this
def C6541 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6541 : C6541.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6541 : ¬ (C6541.det = 0 ∧ ∀ i, C6541.adjugate i i ≠ 0) := by
  intro h
  have := certificate6541
  rw [h.1] at this
  norm_num at this
def C6542 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6542 : C6542.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6542 : ¬ (C6542.det = 0 ∧ ∀ i, C6542.adjugate i i ≠ 0) := by
  intro h
  have := certificate6542
  rw [h.1] at this
  norm_num at this
def C6543 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6543 : C6543.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6543 : ¬ (C6543.det = 0 ∧ ∀ i, C6543.adjugate i i ≠ 0) := by
  intro h
  have := certificate6543
  rw [h.1] at this
  norm_num at this
def C6544 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6544 : C6544.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6544 : ¬ (C6544.det = 0 ∧ ∀ i, C6544.adjugate i i ≠ 0) := by
  intro h
  have := certificate6544
  rw [h.1] at this
  norm_num at this
def C6545 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6545 : C6545.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6545 : ¬ (C6545.det = 0 ∧ ∀ i, C6545.adjugate i i ≠ 0) := by
  intro h
  have := certificate6545
  rw [h.1] at this
  norm_num at this
def C6546 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6546 : C6546.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6546 : ¬ (C6546.det = 0 ∧ ∀ i, C6546.adjugate i i ≠ 0) := by
  intro h
  have := certificate6546
  rw [h.1] at this
  norm_num at this
def C6547 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6547 : C6547.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6547 : ¬ (C6547.det = 0 ∧ ∀ i, C6547.adjugate i i ≠ 0) := by
  intro h
  have := certificate6547
  rw [h.1] at this
  norm_num at this
def C6548 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6548 : C6548.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6548 : ¬ (C6548.det = 0 ∧ ∀ i, C6548.adjugate i i ≠ 0) := by
  intro h
  have := certificate6548
  rw [h.1] at this
  norm_num at this
def C6549 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6549 : C6549.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6549 : ¬ (C6549.det = 0 ∧ ∀ i, C6549.adjugate i i ≠ 0) := by
  intro h
  have := certificate6549
  rw [h.1] at this
  norm_num at this
def C6550 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6550 : C6550.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6550 : ¬ (C6550.det = 0 ∧ ∀ i, C6550.adjugate i i ≠ 0) := by
  intro h
  have := certificate6550
  rw [h.1] at this
  norm_num at this
def C6551 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6551 : C6551.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6551 : ¬ (C6551.det = 0 ∧ ∀ i, C6551.adjugate i i ≠ 0) := by
  intro h
  have := certificate6551
  rw [h.1] at this
  norm_num at this
def C6552 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6552 : C6552.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6552 : ¬ (C6552.det = 0 ∧ ∀ i, C6552.adjugate i i ≠ 0) := by
  intro h
  have := certificate6552
  rw [h.1] at this
  norm_num at this
def C6553 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6553 : C6553.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6553 : ¬ (C6553.det = 0 ∧ ∀ i, C6553.adjugate i i ≠ 0) := by
  intro h
  have := certificate6553
  rw [h.1] at this
  norm_num at this
def C6554 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6554 : C6554.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6554 : ¬ (C6554.det = 0 ∧ ∀ i, C6554.adjugate i i ≠ 0) := by
  intro h
  have := certificate6554
  rw [h.1] at this
  norm_num at this
def C6555 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6555 : C6555.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6555 : ¬ (C6555.det = 0 ∧ ∀ i, C6555.adjugate i i ≠ 0) := by
  intro h
  have := certificate6555
  rw [h.1] at this
  norm_num at this
def C6556 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6556 : C6556.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6556 : ¬ (C6556.det = 0 ∧ ∀ i, C6556.adjugate i i ≠ 0) := by
  intro h
  have := certificate6556
  rw [h.1] at this
  norm_num at this
def C6557 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6557 : C6557.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6557 : ¬ (C6557.det = 0 ∧ ∀ i, C6557.adjugate i i ≠ 0) := by
  intro h
  have := certificate6557
  rw [h.1] at this
  norm_num at this
def C6558 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6558 : C6558.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6558 : ¬ (C6558.det = 0 ∧ ∀ i, C6558.adjugate i i ≠ 0) := by
  intro h
  have := certificate6558
  rw [h.1] at this
  norm_num at this
def C6559 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6559 : C6559.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6559 : ¬ (C6559.det = 0 ∧ ∀ i, C6559.adjugate i i ≠ 0) := by
  intro h
  have := certificate6559
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0204
