import VerifiedDet
namespace Nut8.NewCertificates0201
def C6432 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6432 : C6432.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6432 : ¬ (C6432.det = 0 ∧ ∀ i, C6432.adjugate i i ≠ 0) := by
  intro h
  have := certificate6432
  rw [h.1] at this
  norm_num at this
def C6433 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6433 : C6433.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6433 : ¬ (C6433.det = 0 ∧ ∀ i, C6433.adjugate i i ≠ 0) := by
  intro h
  have := certificate6433
  rw [h.1] at this
  norm_num at this
def C6434 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6434 : C6434.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6434 : ¬ (C6434.det = 0 ∧ ∀ i, C6434.adjugate i i ≠ 0) := by
  intro h
  have := certificate6434
  rw [h.1] at this
  norm_num at this
def C6435 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6435 : C6435.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6435 : ¬ (C6435.det = 0 ∧ ∀ i, C6435.adjugate i i ≠ 0) := by
  intro h
  have := certificate6435
  rw [h.1] at this
  norm_num at this
def C6436 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6436 : C6436.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6436 : ¬ (C6436.det = 0 ∧ ∀ i, C6436.adjugate i i ≠ 0) := by
  intro h
  have := certificate6436
  rw [h.1] at this
  norm_num at this
def C6437 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6437 : C6437.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6437 : ¬ (C6437.det = 0 ∧ ∀ i, C6437.adjugate i i ≠ 0) := by
  intro h
  have := certificate6437
  rw [h.1] at this
  norm_num at this
def C6438 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6438 : C6438.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6438 : ¬ (C6438.det = 0 ∧ ∀ i, C6438.adjugate i i ≠ 0) := by
  intro h
  have := certificate6438
  rw [h.1] at this
  norm_num at this
def C6439 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6439 : C6439.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6439 : ¬ (C6439.det = 0 ∧ ∀ i, C6439.adjugate i i ≠ 0) := by
  intro h
  have := certificate6439
  rw [h.1] at this
  norm_num at this
def C6440 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6440 : C6440.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6440 : ¬ (C6440.det = 0 ∧ ∀ i, C6440.adjugate i i ≠ 0) := by
  intro h
  have := certificate6440
  rw [h.1] at this
  norm_num at this
def C6441 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6441 : C6441.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6441 : ¬ (C6441.det = 0 ∧ ∀ i, C6441.adjugate i i ≠ 0) := by
  intro h
  have := certificate6441
  rw [h.1] at this
  norm_num at this
def C6442 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6442 : C6442.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6442 : ¬ (C6442.det = 0 ∧ ∀ i, C6442.adjugate i i ≠ 0) := by
  intro h
  have := certificate6442
  rw [h.1] at this
  norm_num at this
def C6443 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6443 : C6443.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6443 : ¬ (C6443.det = 0 ∧ ∀ i, C6443.adjugate i i ≠ 0) := by
  intro h
  have := certificate6443
  rw [h.1] at this
  norm_num at this
def C6444 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6444 : C6444.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6444 : ¬ (C6444.det = 0 ∧ ∀ i, C6444.adjugate i i ≠ 0) := by
  intro h
  have := certificate6444
  rw [h.1] at this
  norm_num at this
def C6445 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6445 : C6445.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6445 : ¬ (C6445.det = 0 ∧ ∀ i, C6445.adjugate i i ≠ 0) := by
  intro h
  have := certificate6445
  rw [h.1] at this
  norm_num at this
def C6446 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6446 : C6446.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6446 : ¬ (C6446.det = 0 ∧ ∀ i, C6446.adjugate i i ≠ 0) := by
  intro h
  have := certificate6446
  rw [h.1] at this
  norm_num at this
def C6447 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6447 : C6447.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6447 : ¬ (C6447.det = 0 ∧ ∀ i, C6447.adjugate i i ≠ 0) := by
  intro h
  have := certificate6447
  rw [h.1] at this
  norm_num at this
def C6448 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6448 : C6448.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6448 : ¬ (C6448.det = 0 ∧ ∀ i, C6448.adjugate i i ≠ 0) := by
  intro h
  have := certificate6448
  rw [h.1] at this
  norm_num at this
def C6449 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6449 : C6449.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6449 : ¬ (C6449.det = 0 ∧ ∀ i, C6449.adjugate i i ≠ 0) := by
  intro h
  have := certificate6449
  rw [h.1] at this
  norm_num at this
def C6450 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6450 : C6450.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6450 : ¬ (C6450.det = 0 ∧ ∀ i, C6450.adjugate i i ≠ 0) := by
  intro h
  have := certificate6450
  rw [h.1] at this
  norm_num at this
def C6451 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6451 : C6451.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6451 : ¬ (C6451.det = 0 ∧ ∀ i, C6451.adjugate i i ≠ 0) := by
  intro h
  have := certificate6451
  rw [h.1] at this
  norm_num at this
def C6452 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate6452 : C6452.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6452 : ¬ (C6452.det = 0 ∧ ∀ i, C6452.adjugate i i ≠ 0) := by
  intro h
  have := certificate6452
  rw [h.1] at this
  norm_num at this
def C6453 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate6453 : C6453.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6453 : ¬ (C6453.det = 0 ∧ ∀ i, C6453.adjugate i i ≠ 0) := by
  intro h
  have := certificate6453
  rw [h.1] at this
  norm_num at this
def C6454 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate6454 : C6454.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6454 : ¬ (C6454.det = 0 ∧ ∀ i, C6454.adjugate i i ≠ 0) := by
  intro h
  have := certificate6454
  rw [h.1] at this
  norm_num at this
def C6455 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate6455 : C6455.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6455 : ¬ (C6455.det = 0 ∧ ∀ i, C6455.adjugate i i ≠ 0) := by
  intro h
  have := certificate6455
  rw [h.1] at this
  norm_num at this
def C6456 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate6456 : C6456.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6456 : ¬ (C6456.det = 0 ∧ ∀ i, C6456.adjugate i i ≠ 0) := by
  intro h
  have := certificate6456
  rw [h.1] at this
  norm_num at this
def C6457 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate6457 : C6457.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6457 : ¬ (C6457.det = 0 ∧ ∀ i, C6457.adjugate i i ≠ 0) := by
  intro h
  have := certificate6457
  rw [h.1] at this
  norm_num at this
def C6458 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate6458 : C6458.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6458 : ¬ (C6458.det = 0 ∧ ∀ i, C6458.adjugate i i ≠ 0) := by
  intro h
  have := certificate6458
  rw [h.1] at this
  norm_num at this
def C6459 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate6459 : C6459.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6459 : ¬ (C6459.det = 0 ∧ ∀ i, C6459.adjugate i i ≠ 0) := by
  intro h
  have := certificate6459
  rw [h.1] at this
  norm_num at this
def C6460 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate6460 : C6460.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6460 : ¬ (C6460.det = 0 ∧ ∀ i, C6460.adjugate i i ≠ 0) := by
  intro h
  have := certificate6460
  rw [h.1] at this
  norm_num at this
def C6461 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate6461 : C6461.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6461 : ¬ (C6461.det = 0 ∧ ∀ i, C6461.adjugate i i ≠ 0) := by
  intro h
  have := certificate6461
  rw [h.1] at this
  norm_num at this
def C6462 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate6462 : C6462.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6462 : ¬ (C6462.det = 0 ∧ ∀ i, C6462.adjugate i i ≠ 0) := by
  intro h
  have := certificate6462
  rw [h.1] at this
  norm_num at this
def C6463 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate6463 : C6463.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6463 : ¬ (C6463.det = 0 ∧ ∀ i, C6463.adjugate i i ≠ 0) := by
  intro h
  have := certificate6463
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0201
