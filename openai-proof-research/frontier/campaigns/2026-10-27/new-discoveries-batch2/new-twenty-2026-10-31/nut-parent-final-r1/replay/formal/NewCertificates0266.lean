import VerifiedDet
namespace Nut8.NewCertificates0266
def C8512 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8512 : C8512.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8512 : ¬ (C8512.det = 0 ∧ ∀ i, C8512.adjugate i i ≠ 0) := by
  intro h
  have := certificate8512
  rw [h.1] at this
  norm_num at this
def C8513 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8513 : C8513.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8513 : ¬ (C8513.det = 0 ∧ ∀ i, C8513.adjugate i i ≠ 0) := by
  intro h
  have := certificate8513
  rw [h.1] at this
  norm_num at this
def C8514 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8514 : C8514.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8514 : ¬ (C8514.det = 0 ∧ ∀ i, C8514.adjugate i i ≠ 0) := by
  intro h
  have := certificate8514
  rw [h.1] at this
  norm_num at this
def C8515 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8515 : C8515.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8515 : ¬ (C8515.det = 0 ∧ ∀ i, C8515.adjugate i i ≠ 0) := by
  intro h
  have := certificate8515
  rw [h.1] at this
  norm_num at this
def C8516 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8516 : C8516.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8516 : ¬ (C8516.det = 0 ∧ ∀ i, C8516.adjugate i i ≠ 0) := by
  intro h
  have := certificate8516
  rw [h.1] at this
  norm_num at this
def C8517 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8517 : C8517.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8517 : ¬ (C8517.det = 0 ∧ ∀ i, C8517.adjugate i i ≠ 0) := by
  intro h
  have := certificate8517
  rw [h.1] at this
  norm_num at this
def C8518 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8518 : C8518.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8518 : ¬ (C8518.det = 0 ∧ ∀ i, C8518.adjugate i i ≠ 0) := by
  intro h
  have := certificate8518
  rw [h.1] at this
  norm_num at this
def C8519 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8519 : C8519.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8519 : ¬ (C8519.det = 0 ∧ ∀ i, C8519.adjugate i i ≠ 0) := by
  intro h
  have := certificate8519
  rw [h.1] at this
  norm_num at this
def C8520 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8520 : C8520.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8520 : ¬ (C8520.det = 0 ∧ ∀ i, C8520.adjugate i i ≠ 0) := by
  intro h
  have := certificate8520
  rw [h.1] at this
  norm_num at this
def C8521 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8521 : C8521.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8521 : ¬ (C8521.det = 0 ∧ ∀ i, C8521.adjugate i i ≠ 0) := by
  intro h
  have := certificate8521
  rw [h.1] at this
  norm_num at this
def C8522 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8522 : C8522.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8522 : ¬ (C8522.det = 0 ∧ ∀ i, C8522.adjugate i i ≠ 0) := by
  intro h
  have := certificate8522
  rw [h.1] at this
  norm_num at this
def C8523 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8523 : C8523.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8523 : ¬ (C8523.det = 0 ∧ ∀ i, C8523.adjugate i i ≠ 0) := by
  intro h
  have := certificate8523
  rw [h.1] at this
  norm_num at this
def C8524 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8524 : C8524.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8524 : ¬ (C8524.det = 0 ∧ ∀ i, C8524.adjugate i i ≠ 0) := by
  intro h
  have := certificate8524
  rw [h.1] at this
  norm_num at this
def C8525 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8525 : C8525.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8525 : ¬ (C8525.det = 0 ∧ ∀ i, C8525.adjugate i i ≠ 0) := by
  intro h
  have := certificate8525
  rw [h.1] at this
  norm_num at this
def C8526 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8526 : C8526.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8526 : ¬ (C8526.det = 0 ∧ ∀ i, C8526.adjugate i i ≠ 0) := by
  intro h
  have := certificate8526
  rw [h.1] at this
  norm_num at this
def C8527 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8527 : C8527.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8527 : ¬ (C8527.det = 0 ∧ ∀ i, C8527.adjugate i i ≠ 0) := by
  intro h
  have := certificate8527
  rw [h.1] at this
  norm_num at this
def C8528 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8528 : C8528.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8528 : ¬ (C8528.det = 0 ∧ ∀ i, C8528.adjugate i i ≠ 0) := by
  intro h
  have := certificate8528
  rw [h.1] at this
  norm_num at this
def C8529 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8529 : C8529.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8529 : ¬ (C8529.det = 0 ∧ ∀ i, C8529.adjugate i i ≠ 0) := by
  intro h
  have := certificate8529
  rw [h.1] at this
  norm_num at this
def C8530 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8530 : C8530.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8530 : ¬ (C8530.det = 0 ∧ ∀ i, C8530.adjugate i i ≠ 0) := by
  intro h
  have := certificate8530
  rw [h.1] at this
  norm_num at this
def C8531 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8531 : C8531.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8531 : ¬ (C8531.det = 0 ∧ ∀ i, C8531.adjugate i i ≠ 0) := by
  intro h
  have := certificate8531
  rw [h.1] at this
  norm_num at this
def C8532 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8532 : C8532.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8532 : ¬ (C8532.det = 0 ∧ ∀ i, C8532.adjugate i i ≠ 0) := by
  intro h
  have := certificate8532
  rw [h.1] at this
  norm_num at this
def C8533 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8533 : C8533.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8533 : ¬ (C8533.det = 0 ∧ ∀ i, C8533.adjugate i i ≠ 0) := by
  intro h
  have := certificate8533
  rw [h.1] at this
  norm_num at this
def C8534 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8534 : C8534.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8534 : ¬ (C8534.det = 0 ∧ ∀ i, C8534.adjugate i i ≠ 0) := by
  intro h
  have := certificate8534
  rw [h.1] at this
  norm_num at this
def C8535 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8535 : C8535.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8535 : ¬ (C8535.det = 0 ∧ ∀ i, C8535.adjugate i i ≠ 0) := by
  intro h
  have := certificate8535
  rw [h.1] at this
  norm_num at this
def C8536 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8536 : C8536.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8536 : ¬ (C8536.det = 0 ∧ ∀ i, C8536.adjugate i i ≠ 0) := by
  intro h
  have := certificate8536
  rw [h.1] at this
  norm_num at this
def C8537 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8537 : C8537.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8537 : ¬ (C8537.det = 0 ∧ ∀ i, C8537.adjugate i i ≠ 0) := by
  intro h
  have := certificate8537
  rw [h.1] at this
  norm_num at this
def C8538 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8538 : C8538.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8538 : ¬ (C8538.det = 0 ∧ ∀ i, C8538.adjugate i i ≠ 0) := by
  intro h
  have := certificate8538
  rw [h.1] at this
  norm_num at this
def C8539 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8539 : C8539.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8539 : ¬ (C8539.det = 0 ∧ ∀ i, C8539.adjugate i i ≠ 0) := by
  intro h
  have := certificate8539
  rw [h.1] at this
  norm_num at this
def C8540 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8540 : C8540.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8540 : ¬ (C8540.det = 0 ∧ ∀ i, C8540.adjugate i i ≠ 0) := by
  intro h
  have := certificate8540
  rw [h.1] at this
  norm_num at this
def C8541 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8541 : C8541.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8541 : ¬ (C8541.det = 0 ∧ ∀ i, C8541.adjugate i i ≠ 0) := by
  intro h
  have := certificate8541
  rw [h.1] at this
  norm_num at this
def C8542 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8542 : C8542.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8542 : ¬ (C8542.det = 0 ∧ ∀ i, C8542.adjugate i i ≠ 0) := by
  intro h
  have := certificate8542
  rw [h.1] at this
  norm_num at this
def C8543 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8543 : C8543.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8543 : ¬ (C8543.det = 0 ∧ ∀ i, C8543.adjugate i i ≠ 0) := by
  intro h
  have := certificate8543
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0266
