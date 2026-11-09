import VerifiedDet
namespace Nut8.NewCertificates0203
def C6496 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6496 : C6496.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6496 : ¬ (C6496.det = 0 ∧ ∀ i, C6496.adjugate i i ≠ 0) := by
  intro h
  have := certificate6496
  rw [h.1] at this
  norm_num at this
def C6497 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6497 : C6497.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6497 : ¬ (C6497.det = 0 ∧ ∀ i, C6497.adjugate i i ≠ 0) := by
  intro h
  have := certificate6497
  rw [h.1] at this
  norm_num at this
def C6498 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6498 : C6498.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6498 : ¬ (C6498.det = 0 ∧ ∀ i, C6498.adjugate i i ≠ 0) := by
  intro h
  have := certificate6498
  rw [h.1] at this
  norm_num at this
def C6499 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6499 : C6499.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6499 : ¬ (C6499.det = 0 ∧ ∀ i, C6499.adjugate i i ≠ 0) := by
  intro h
  have := certificate6499
  rw [h.1] at this
  norm_num at this
def C6500 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6500 : C6500.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6500 : ¬ (C6500.det = 0 ∧ ∀ i, C6500.adjugate i i ≠ 0) := by
  intro h
  have := certificate6500
  rw [h.1] at this
  norm_num at this
def C6501 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6501 : C6501.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6501 : ¬ (C6501.det = 0 ∧ ∀ i, C6501.adjugate i i ≠ 0) := by
  intro h
  have := certificate6501
  rw [h.1] at this
  norm_num at this
def C6502 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6502 : C6502.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6502 : ¬ (C6502.det = 0 ∧ ∀ i, C6502.adjugate i i ≠ 0) := by
  intro h
  have := certificate6502
  rw [h.1] at this
  norm_num at this
def C6503 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6503 : C6503.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6503 : ¬ (C6503.det = 0 ∧ ∀ i, C6503.adjugate i i ≠ 0) := by
  intro h
  have := certificate6503
  rw [h.1] at this
  norm_num at this
def C6504 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6504 : C6504.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6504 : ¬ (C6504.det = 0 ∧ ∀ i, C6504.adjugate i i ≠ 0) := by
  intro h
  have := certificate6504
  rw [h.1] at this
  norm_num at this
def C6505 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6505 : C6505.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6505 : ¬ (C6505.det = 0 ∧ ∀ i, C6505.adjugate i i ≠ 0) := by
  intro h
  have := certificate6505
  rw [h.1] at this
  norm_num at this
def C6506 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6506 : C6506.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6506 : ¬ (C6506.det = 0 ∧ ∀ i, C6506.adjugate i i ≠ 0) := by
  intro h
  have := certificate6506
  rw [h.1] at this
  norm_num at this
def C6507 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6507 : C6507.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6507 : ¬ (C6507.det = 0 ∧ ∀ i, C6507.adjugate i i ≠ 0) := by
  intro h
  have := certificate6507
  rw [h.1] at this
  norm_num at this
def C6508 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6508 : C6508.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6508 : ¬ (C6508.det = 0 ∧ ∀ i, C6508.adjugate i i ≠ 0) := by
  intro h
  have := certificate6508
  rw [h.1] at this
  norm_num at this
def C6509 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6509 : C6509.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6509 : ¬ (C6509.det = 0 ∧ ∀ i, C6509.adjugate i i ≠ 0) := by
  intro h
  have := certificate6509
  rw [h.1] at this
  norm_num at this
def C6510 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6510 : C6510.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6510 : ¬ (C6510.det = 0 ∧ ∀ i, C6510.adjugate i i ≠ 0) := by
  intro h
  have := certificate6510
  rw [h.1] at this
  norm_num at this
def C6511 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6511 : C6511.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6511 : ¬ (C6511.det = 0 ∧ ∀ i, C6511.adjugate i i ≠ 0) := by
  intro h
  have := certificate6511
  rw [h.1] at this
  norm_num at this
def C6512 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6512 : C6512.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6512 : ¬ (C6512.det = 0 ∧ ∀ i, C6512.adjugate i i ≠ 0) := by
  intro h
  have := certificate6512
  rw [h.1] at this
  norm_num at this
def C6513 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6513 : C6513.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6513 : ¬ (C6513.det = 0 ∧ ∀ i, C6513.adjugate i i ≠ 0) := by
  intro h
  have := certificate6513
  rw [h.1] at this
  norm_num at this
def C6514 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6514 : C6514.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6514 : ¬ (C6514.det = 0 ∧ ∀ i, C6514.adjugate i i ≠ 0) := by
  intro h
  have := certificate6514
  rw [h.1] at this
  norm_num at this
def C6515 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6515 : C6515.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6515 : ¬ (C6515.det = 0 ∧ ∀ i, C6515.adjugate i i ≠ 0) := by
  intro h
  have := certificate6515
  rw [h.1] at this
  norm_num at this
def C6516 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6516 : C6516.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6516 : ¬ (C6516.det = 0 ∧ ∀ i, C6516.adjugate i i ≠ 0) := by
  intro h
  have := certificate6516
  rw [h.1] at this
  norm_num at this
def C6517 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6517 : C6517.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6517 : ¬ (C6517.det = 0 ∧ ∀ i, C6517.adjugate i i ≠ 0) := by
  intro h
  have := certificate6517
  rw [h.1] at this
  norm_num at this
def C6518 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6518 : C6518.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6518 : ¬ (C6518.det = 0 ∧ ∀ i, C6518.adjugate i i ≠ 0) := by
  intro h
  have := certificate6518
  rw [h.1] at this
  norm_num at this
def C6519 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6519 : C6519.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6519 : ¬ (C6519.det = 0 ∧ ∀ i, C6519.adjugate i i ≠ 0) := by
  intro h
  have := certificate6519
  rw [h.1] at this
  norm_num at this
def C6520 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6520 : C6520.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6520 : ¬ (C6520.det = 0 ∧ ∀ i, C6520.adjugate i i ≠ 0) := by
  intro h
  have := certificate6520
  rw [h.1] at this
  norm_num at this
def C6521 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6521 : C6521.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6521 : ¬ (C6521.det = 0 ∧ ∀ i, C6521.adjugate i i ≠ 0) := by
  intro h
  have := certificate6521
  rw [h.1] at this
  norm_num at this
def C6522 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6522 : C6522.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6522 : ¬ (C6522.det = 0 ∧ ∀ i, C6522.adjugate i i ≠ 0) := by
  intro h
  have := certificate6522
  rw [h.1] at this
  norm_num at this
def C6523 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6523 : C6523.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6523 : ¬ (C6523.det = 0 ∧ ∀ i, C6523.adjugate i i ≠ 0) := by
  intro h
  have := certificate6523
  rw [h.1] at this
  norm_num at this
def C6524 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6524 : C6524.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6524 : ¬ (C6524.det = 0 ∧ ∀ i, C6524.adjugate i i ≠ 0) := by
  intro h
  have := certificate6524
  rw [h.1] at this
  norm_num at this
def C6525 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6525 : C6525.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6525 : ¬ (C6525.det = 0 ∧ ∀ i, C6525.adjugate i i ≠ 0) := by
  intro h
  have := certificate6525
  rw [h.1] at this
  norm_num at this
def C6526 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6526 : C6526.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6526 : ¬ (C6526.det = 0 ∧ ∀ i, C6526.adjugate i i ≠ 0) := by
  intro h
  have := certificate6526
  rw [h.1] at this
  norm_num at this
def C6527 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6527 : C6527.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6527 : ¬ (C6527.det = 0 ∧ ∀ i, C6527.adjugate i i ≠ 0) := by
  intro h
  have := certificate6527
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0203
