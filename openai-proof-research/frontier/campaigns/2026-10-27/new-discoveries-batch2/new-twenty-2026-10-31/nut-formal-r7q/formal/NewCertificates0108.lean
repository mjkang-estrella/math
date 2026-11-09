import VerifiedDet
namespace Nut8.NewCertificates0108
def C3456 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3456 : C3456.det = (38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3456 : ¬ (C3456.det = 0 ∧ ∀ i, C3456.adjugate i i ≠ 0) := by
  intro h
  have := certificate3456
  rw [h.1] at this
  norm_num at this
def C3457 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3457 : C3457.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3457 : ¬ (C3457.det = 0 ∧ ∀ i, C3457.adjugate i i ≠ 0) := by
  intro h
  have := certificate3457
  rw [h.1] at this
  norm_num at this
def C3458 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3458 : C3458.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3458 : ¬ (C3458.det = 0 ∧ ∀ i, C3458.adjugate i i ≠ 0) := by
  intro h
  have := certificate3458
  rw [h.1] at this
  norm_num at this
def C3459 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3459 : C3459.det = (86 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3459 : ¬ (C3459.det = 0 ∧ ∀ i, C3459.adjugate i i ≠ 0) := by
  intro h
  have := certificate3459
  rw [h.1] at this
  norm_num at this
def C3460 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3460 : C3460.det = (86 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3460 : ¬ (C3460.det = 0 ∧ ∀ i, C3460.adjugate i i ≠ 0) := by
  intro h
  have := certificate3460
  rw [h.1] at this
  norm_num at this
def C3461 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3461 : C3461.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3461 : ¬ (C3461.det = 0 ∧ ∀ i, C3461.adjugate i i ≠ 0) := by
  intro h
  have := certificate3461
  rw [h.1] at this
  norm_num at this
def C3462 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3462 : C3462.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3462 : ¬ (C3462.det = 0 ∧ ∀ i, C3462.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3462
def C3463 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3463 : C3463.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3463 : ¬ (C3463.det = 0 ∧ ∀ i, C3463.adjugate i i ≠ 0) := by
  intro h
  have := certificate3463
  rw [h.1] at this
  norm_num at this
def C3464 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3464 : C3464.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3464 : ¬ (C3464.det = 0 ∧ ∀ i, C3464.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3464
def C3465 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3465 : C3465.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3465 : ¬ (C3465.det = 0 ∧ ∀ i, C3465.adjugate i i ≠ 0) := by
  intro h
  have := certificate3465
  rw [h.1] at this
  norm_num at this
def C3466 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3466 : C3466.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3466 : ¬ (C3466.det = 0 ∧ ∀ i, C3466.adjugate i i ≠ 0) := by
  intro h
  have := certificate3466
  rw [h.1] at this
  norm_num at this
def C3467 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3467 : C3467.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3467 : ¬ (C3467.det = 0 ∧ ∀ i, C3467.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3467
def C3468 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3468 : C3468.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3468 : ¬ (C3468.det = 0 ∧ ∀ i, C3468.adjugate i i ≠ 0) := by
  intro h
  have := certificate3468
  rw [h.1] at this
  norm_num at this
def C3469 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3469 : C3469.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3469 : ¬ (C3469.det = 0 ∧ ∀ i, C3469.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3469
def C3470 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3470 : C3470.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3470 : ¬ (C3470.det = 0 ∧ ∀ i, C3470.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3470
def C3471 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3471 : C3471.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3471 : ¬ (C3471.det = 0 ∧ ∀ i, C3471.adjugate i i ≠ 0) := by
  intro h
  have := certificate3471
  rw [h.1] at this
  norm_num at this
def C3472 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3472 : C3472.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3472 : ¬ (C3472.det = 0 ∧ ∀ i, C3472.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3472
def C3473 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3473 : C3473.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3473 : ¬ (C3473.det = 0 ∧ ∀ i, C3473.adjugate i i ≠ 0) := by
  intro h
  have := certificate3473
  rw [h.1] at this
  norm_num at this
def C3474 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3474 : C3474.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3474 : ¬ (C3474.det = 0 ∧ ∀ i, C3474.adjugate i i ≠ 0) := by
  intro h
  have := certificate3474
  rw [h.1] at this
  norm_num at this
def C3475 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3475 : C3475.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3475 : ¬ (C3475.det = 0 ∧ ∀ i, C3475.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3475
def C3476 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3476 : C3476.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3476 : ¬ (C3476.det = 0 ∧ ∀ i, C3476.adjugate i i ≠ 0) := by
  intro h
  have := certificate3476
  rw [h.1] at this
  norm_num at this
def C3477 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3477 : C3477.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3477 : ¬ (C3477.det = 0 ∧ ∀ i, C3477.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3477
def C3478 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3478 : C3478.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3478 : ¬ (C3478.det = 0 ∧ ∀ i, C3478.adjugate i i ≠ 0) := by
  intro h
  have := certificate3478
  rw [h.1] at this
  norm_num at this
def C3479 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3479 : C3479.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3479 : ¬ (C3479.det = 0 ∧ ∀ i, C3479.adjugate i i ≠ 0) := by
  intro h
  have := certificate3479
  rw [h.1] at this
  norm_num at this
def C3480 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3480 : C3480.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3480 : ¬ (C3480.det = 0 ∧ ∀ i, C3480.adjugate i i ≠ 0) := by
  intro h
  have := certificate3480
  rw [h.1] at this
  norm_num at this
def C3481 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3481 : C3481.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3481 : ¬ (C3481.det = 0 ∧ ∀ i, C3481.adjugate i i ≠ 0) := by
  intro h
  have := certificate3481
  rw [h.1] at this
  norm_num at this
def C3482 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3482 : C3482.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3482 : ¬ (C3482.det = 0 ∧ ∀ i, C3482.adjugate i i ≠ 0) := by
  intro h
  have := certificate3482
  rw [h.1] at this
  norm_num at this
def C3483 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3483 : C3483.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3483 : ¬ (C3483.det = 0 ∧ ∀ i, C3483.adjugate i i ≠ 0) := by
  intro h
  have := certificate3483
  rw [h.1] at this
  norm_num at this
def C3484 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3484 : C3484.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3484 : ¬ (C3484.det = 0 ∧ ∀ i, C3484.adjugate i i ≠ 0) := by
  intro h
  have := certificate3484
  rw [h.1] at this
  norm_num at this
def C3485 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3485 : C3485.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3485 : ¬ (C3485.det = 0 ∧ ∀ i, C3485.adjugate i i ≠ 0) := by
  intro h
  have := certificate3485
  rw [h.1] at this
  norm_num at this
def C3486 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3486 : C3486.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3486 : ¬ (C3486.det = 0 ∧ ∀ i, C3486.adjugate i i ≠ 0) := by
  intro h
  have := certificate3486
  rw [h.1] at this
  norm_num at this
def C3487 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3487 : C3487.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3487 : ¬ (C3487.det = 0 ∧ ∀ i, C3487.adjugate i i ≠ 0) := by
  intro h
  have := certificate3487
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0108
