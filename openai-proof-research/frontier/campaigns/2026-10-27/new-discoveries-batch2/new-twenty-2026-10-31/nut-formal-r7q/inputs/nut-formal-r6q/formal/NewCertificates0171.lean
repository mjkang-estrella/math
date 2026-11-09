import VerifiedDet
namespace Nut8.NewCertificates0171
def C5472 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5472 : C5472.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5472 : ¬ (C5472.det = 0 ∧ ∀ i, C5472.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5472
def C5473 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5473 : C5473.det = (128 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5473 : ¬ (C5473.det = 0 ∧ ∀ i, C5473.adjugate i i ≠ 0) := by
  intro h
  have := certificate5473
  rw [h.1] at this
  norm_num at this
def C5474 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5474 : C5474.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5474 : ¬ (C5474.det = 0 ∧ ∀ i, C5474.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5474
def C5475 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5475 : C5475.det = (-128 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5475 : ¬ (C5475.det = 0 ∧ ∀ i, C5475.adjugate i i ≠ 0) := by
  intro h
  have := certificate5475
  rw [h.1] at this
  norm_num at this
def C5476 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5476 : C5476.det = (-128 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5476 : ¬ (C5476.det = 0 ∧ ∀ i, C5476.adjugate i i ≠ 0) := by
  intro h
  have := certificate5476
  rw [h.1] at this
  norm_num at this
def C5477 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5477 : C5477.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5477 : ¬ (C5477.det = 0 ∧ ∀ i, C5477.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5477
def C5478 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5478 : C5478.det = (128 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5478 : ¬ (C5478.det = 0 ∧ ∀ i, C5478.adjugate i i ≠ 0) := by
  intro h
  have := certificate5478
  rw [h.1] at this
  norm_num at this
def C5479 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5479 : C5479.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5479 : ¬ (C5479.det = 0 ∧ ∀ i, C5479.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5479
def C5480 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5480 : C5480.det = (132 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5480 : ¬ (C5480.det = 0 ∧ ∀ i, C5480.adjugate i i ≠ 0) := by
  intro h
  have := certificate5480
  rw [h.1] at this
  norm_num at this
def C5481 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5481 : C5481.det = (-124 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5481 : ¬ (C5481.det = 0 ∧ ∀ i, C5481.adjugate i i ≠ 0) := by
  intro h
  have := certificate5481
  rw [h.1] at this
  norm_num at this
def C5482 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5482 : C5482.det = (-124 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5482 : ¬ (C5482.det = 0 ∧ ∀ i, C5482.adjugate i i ≠ 0) := by
  intro h
  have := certificate5482
  rw [h.1] at this
  norm_num at this
def C5483 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5483 : C5483.det = (132 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5483 : ¬ (C5483.det = 0 ∧ ∀ i, C5483.adjugate i i ≠ 0) := by
  intro h
  have := certificate5483
  rw [h.1] at this
  norm_num at this
def C5484 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5484 : C5484.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5484 : ¬ (C5484.det = 0 ∧ ∀ i, C5484.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5484
def C5485 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5485 : C5485.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5485 : ¬ (C5485.det = 0 ∧ ∀ i, C5485.adjugate i i ≠ 0) := by
  intro h
  have := certificate5485
  rw [h.1] at this
  norm_num at this
def C5486 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5486 : C5486.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5486 : ¬ (C5486.det = 0 ∧ ∀ i, C5486.adjugate i i ≠ 0) := by
  intro h
  have := certificate5486
  rw [h.1] at this
  norm_num at this
def C5487 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5487 : C5487.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5487 : ¬ (C5487.det = 0 ∧ ∀ i, C5487.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5487
def C5488 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5488 : C5488.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5488 : ¬ (C5488.det = 0 ∧ ∀ i, C5488.adjugate i i ≠ 0) := by
  intro h
  have := certificate5488
  rw [h.1] at this
  norm_num at this
def C5489 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5489 : C5489.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5489 : ¬ (C5489.det = 0 ∧ ∀ i, C5489.adjugate i i ≠ 0) := by
  intro h
  have := certificate5489
  rw [h.1] at this
  norm_num at this
def C5490 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5490 : C5490.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5490 : ¬ (C5490.det = 0 ∧ ∀ i, C5490.adjugate i i ≠ 0) := by
  intro h
  have := certificate5490
  rw [h.1] at this
  norm_num at this
def C5491 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5491 : C5491.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5491 : ¬ (C5491.det = 0 ∧ ∀ i, C5491.adjugate i i ≠ 0) := by
  intro h
  have := certificate5491
  rw [h.1] at this
  norm_num at this
def C5492 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5492 : C5492.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5492 : ¬ (C5492.det = 0 ∧ ∀ i, C5492.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5492
def C5493 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5493 : C5493.det = (-80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5493 : ¬ (C5493.det = 0 ∧ ∀ i, C5493.adjugate i i ≠ 0) := by
  intro h
  have := certificate5493
  rw [h.1] at this
  norm_num at this
def C5494 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5494 : C5494.det = (-80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5494 : ¬ (C5494.det = 0 ∧ ∀ i, C5494.adjugate i i ≠ 0) := by
  intro h
  have := certificate5494
  rw [h.1] at this
  norm_num at this
def C5495 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5495 : C5495.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5495 : ¬ (C5495.det = 0 ∧ ∀ i, C5495.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5495
def C5496 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5496 : C5496.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5496 : ¬ (C5496.det = 0 ∧ ∀ i, C5496.adjugate i i ≠ 0) := by
  intro h
  have := certificate5496
  rw [h.1] at this
  norm_num at this
def C5497 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5497 : C5497.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5497 : ¬ (C5497.det = 0 ∧ ∀ i, C5497.adjugate i i ≠ 0) := by
  intro h
  have := certificate5497
  rw [h.1] at this
  norm_num at this
def C5498 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5498 : C5498.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5498 : ¬ (C5498.det = 0 ∧ ∀ i, C5498.adjugate i i ≠ 0) := by
  intro h
  have := certificate5498
  rw [h.1] at this
  norm_num at this
def C5499 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5499 : C5499.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5499 : ¬ (C5499.det = 0 ∧ ∀ i, C5499.adjugate i i ≠ 0) := by
  intro h
  have := certificate5499
  rw [h.1] at this
  norm_num at this
def C5500 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5500 : C5500.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5500 : ¬ (C5500.det = 0 ∧ ∀ i, C5500.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5500
def C5501 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5501 : C5501.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5501 : ¬ (C5501.det = 0 ∧ ∀ i, C5501.adjugate i i ≠ 0) := by
  intro h
  have := certificate5501
  rw [h.1] at this
  norm_num at this
def C5502 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5502 : C5502.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5502 : ¬ (C5502.det = 0 ∧ ∀ i, C5502.adjugate i i ≠ 0) := by
  intro h
  have := certificate5502
  rw [h.1] at this
  norm_num at this
def C5503 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5503 : C5503.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5503 : ¬ (C5503.det = 0 ∧ ∀ i, C5503.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5503
end Nut8.NewCertificates0171
