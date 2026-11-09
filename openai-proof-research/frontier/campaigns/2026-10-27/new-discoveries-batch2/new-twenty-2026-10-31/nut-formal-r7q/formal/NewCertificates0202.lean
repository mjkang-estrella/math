import VerifiedDet
namespace Nut8.NewCertificates0202
def C6464 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate6464 : C6464.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6464 : ¬ (C6464.det = 0 ∧ ∀ i, C6464.adjugate i i ≠ 0) := by
  intro h
  have := certificate6464
  rw [h.1] at this
  norm_num at this
def C6465 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate6465 : C6465.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6465 : ¬ (C6465.det = 0 ∧ ∀ i, C6465.adjugate i i ≠ 0) := by
  intro h
  have := certificate6465
  rw [h.1] at this
  norm_num at this
def C6466 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate6466 : C6466.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6466 : ¬ (C6466.det = 0 ∧ ∀ i, C6466.adjugate i i ≠ 0) := by
  intro h
  have := certificate6466
  rw [h.1] at this
  norm_num at this
def C6467 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate6467 : C6467.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6467 : ¬ (C6467.det = 0 ∧ ∀ i, C6467.adjugate i i ≠ 0) := by
  intro h
  have := certificate6467
  rw [h.1] at this
  norm_num at this
def C6468 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate6468 : C6468.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6468 : ¬ (C6468.det = 0 ∧ ∀ i, C6468.adjugate i i ≠ 0) := by
  intro h
  have := certificate6468
  rw [h.1] at this
  norm_num at this
def C6469 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate6469 : C6469.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6469 : ¬ (C6469.det = 0 ∧ ∀ i, C6469.adjugate i i ≠ 0) := by
  intro h
  have := certificate6469
  rw [h.1] at this
  norm_num at this
def C6470 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate6470 : C6470.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6470 : ¬ (C6470.det = 0 ∧ ∀ i, C6470.adjugate i i ≠ 0) := by
  intro h
  have := certificate6470
  rw [h.1] at this
  norm_num at this
def C6471 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate6471 : C6471.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6471 : ¬ (C6471.det = 0 ∧ ∀ i, C6471.adjugate i i ≠ 0) := by
  intro h
  have := certificate6471
  rw [h.1] at this
  norm_num at this
def C6472 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate6472 : C6472.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6472 : ¬ (C6472.det = 0 ∧ ∀ i, C6472.adjugate i i ≠ 0) := by
  intro h
  have := certificate6472
  rw [h.1] at this
  norm_num at this
def C6473 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate6473 : C6473.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6473 : ¬ (C6473.det = 0 ∧ ∀ i, C6473.adjugate i i ≠ 0) := by
  intro h
  have := certificate6473
  rw [h.1] at this
  norm_num at this
def C6474 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate6474 : C6474.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6474 : ¬ (C6474.det = 0 ∧ ∀ i, C6474.adjugate i i ≠ 0) := by
  intro h
  have := certificate6474
  rw [h.1] at this
  norm_num at this
def C6475 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate6475 : C6475.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6475 : ¬ (C6475.det = 0 ∧ ∀ i, C6475.adjugate i i ≠ 0) := by
  intro h
  have := certificate6475
  rw [h.1] at this
  norm_num at this
def C6476 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate6476 : C6476.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6476 : ¬ (C6476.det = 0 ∧ ∀ i, C6476.adjugate i i ≠ 0) := by
  intro h
  have := certificate6476
  rw [h.1] at this
  norm_num at this
def C6477 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate6477 : C6477.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6477 : ¬ (C6477.det = 0 ∧ ∀ i, C6477.adjugate i i ≠ 0) := by
  intro h
  have := certificate6477
  rw [h.1] at this
  norm_num at this
def C6478 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate6478 : C6478.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6478 : ¬ (C6478.det = 0 ∧ ∀ i, C6478.adjugate i i ≠ 0) := by
  intro h
  have := certificate6478
  rw [h.1] at this
  norm_num at this
def C6479 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate6479 : C6479.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6479 : ¬ (C6479.det = 0 ∧ ∀ i, C6479.adjugate i i ≠ 0) := by
  intro h
  have := certificate6479
  rw [h.1] at this
  norm_num at this
def C6480 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate6480 : C6480.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6480 : ¬ (C6480.det = 0 ∧ ∀ i, C6480.adjugate i i ≠ 0) := by
  intro h
  have := certificate6480
  rw [h.1] at this
  norm_num at this
def C6481 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate6481 : C6481.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6481 : ¬ (C6481.det = 0 ∧ ∀ i, C6481.adjugate i i ≠ 0) := by
  intro h
  have := certificate6481
  rw [h.1] at this
  norm_num at this
def C6482 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate6482 : C6482.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6482 : ¬ (C6482.det = 0 ∧ ∀ i, C6482.adjugate i i ≠ 0) := by
  intro h
  have := certificate6482
  rw [h.1] at this
  norm_num at this
def C6483 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate6483 : C6483.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6483 : ¬ (C6483.det = 0 ∧ ∀ i, C6483.adjugate i i ≠ 0) := by
  intro h
  have := certificate6483
  rw [h.1] at this
  norm_num at this
def C6484 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6484 : C6484.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6484 : ¬ (C6484.det = 0 ∧ ∀ i, C6484.adjugate i i ≠ 0) := by
  intro h
  have := certificate6484
  rw [h.1] at this
  norm_num at this
def C6485 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6485 : C6485.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6485 : ¬ (C6485.det = 0 ∧ ∀ i, C6485.adjugate i i ≠ 0) := by
  intro h
  have := certificate6485
  rw [h.1] at this
  norm_num at this
def C6486 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6486 : C6486.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6486 : ¬ (C6486.det = 0 ∧ ∀ i, C6486.adjugate i i ≠ 0) := by
  intro h
  have := certificate6486
  rw [h.1] at this
  norm_num at this
def C6487 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6487 : C6487.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6487 : ¬ (C6487.det = 0 ∧ ∀ i, C6487.adjugate i i ≠ 0) := by
  intro h
  have := certificate6487
  rw [h.1] at this
  norm_num at this
def C6488 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6488 : C6488.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6488 : ¬ (C6488.det = 0 ∧ ∀ i, C6488.adjugate i i ≠ 0) := by
  intro h
  have := certificate6488
  rw [h.1] at this
  norm_num at this
def C6489 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6489 : C6489.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6489 : ¬ (C6489.det = 0 ∧ ∀ i, C6489.adjugate i i ≠ 0) := by
  intro h
  have := certificate6489
  rw [h.1] at this
  norm_num at this
def C6490 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6490 : C6490.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6490 : ¬ (C6490.det = 0 ∧ ∀ i, C6490.adjugate i i ≠ 0) := by
  intro h
  have := certificate6490
  rw [h.1] at this
  norm_num at this
def C6491 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6491 : C6491.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6491 : ¬ (C6491.det = 0 ∧ ∀ i, C6491.adjugate i i ≠ 0) := by
  intro h
  have := certificate6491
  rw [h.1] at this
  norm_num at this
def C6492 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6492 : C6492.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6492 : ¬ (C6492.det = 0 ∧ ∀ i, C6492.adjugate i i ≠ 0) := by
  intro h
  have := certificate6492
  rw [h.1] at this
  norm_num at this
def C6493 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6493 : C6493.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6493 : ¬ (C6493.det = 0 ∧ ∀ i, C6493.adjugate i i ≠ 0) := by
  intro h
  have := certificate6493
  rw [h.1] at this
  norm_num at this
def C6494 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6494 : C6494.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6494 : ¬ (C6494.det = 0 ∧ ∀ i, C6494.adjugate i i ≠ 0) := by
  intro h
  have := certificate6494
  rw [h.1] at this
  norm_num at this
def C6495 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6495 : C6495.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6495 : ¬ (C6495.det = 0 ∧ ∀ i, C6495.adjugate i i ≠ 0) := by
  intro h
  have := certificate6495
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0202
