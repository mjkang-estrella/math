import VerifiedDet
namespace Nut8.NewCertificates0233
def C7456 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7456 : C7456.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7456 : ¬ (C7456.det = 0 ∧ ∀ i, C7456.adjugate i i ≠ 0) := by
  intro h
  have := certificate7456
  rw [h.1] at this
  norm_num at this
def C7457 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7457 : C7457.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7457 : ¬ (C7457.det = 0 ∧ ∀ i, C7457.adjugate i i ≠ 0) := by
  intro h
  have := certificate7457
  rw [h.1] at this
  norm_num at this
def C7458 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7458 : C7458.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7458 : ¬ (C7458.det = 0 ∧ ∀ i, C7458.adjugate i i ≠ 0) := by
  intro h
  have := certificate7458
  rw [h.1] at this
  norm_num at this
def C7459 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7459 : C7459.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7459 : ¬ (C7459.det = 0 ∧ ∀ i, C7459.adjugate i i ≠ 0) := by
  intro h
  have := certificate7459
  rw [h.1] at this
  norm_num at this
def C7460 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7460 : C7460.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7460 : ¬ (C7460.det = 0 ∧ ∀ i, C7460.adjugate i i ≠ 0) := by
  intro h
  have := certificate7460
  rw [h.1] at this
  norm_num at this
def C7461 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7461 : C7461.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7461 : ¬ (C7461.det = 0 ∧ ∀ i, C7461.adjugate i i ≠ 0) := by
  intro h
  have := certificate7461
  rw [h.1] at this
  norm_num at this
def C7462 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7462 : C7462.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7462 : ¬ (C7462.det = 0 ∧ ∀ i, C7462.adjugate i i ≠ 0) := by
  intro h
  have := certificate7462
  rw [h.1] at this
  norm_num at this
def C7463 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7463 : C7463.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7463 : ¬ (C7463.det = 0 ∧ ∀ i, C7463.adjugate i i ≠ 0) := by
  intro h
  have := certificate7463
  rw [h.1] at this
  norm_num at this
def C7464 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7464 : C7464.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7464 : ¬ (C7464.det = 0 ∧ ∀ i, C7464.adjugate i i ≠ 0) := by
  intro h
  have := certificate7464
  rw [h.1] at this
  norm_num at this
def C7465 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7465 : C7465.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7465 : ¬ (C7465.det = 0 ∧ ∀ i, C7465.adjugate i i ≠ 0) := by
  intro h
  have := certificate7465
  rw [h.1] at this
  norm_num at this
def C7466 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7466 : C7466.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7466 : ¬ (C7466.det = 0 ∧ ∀ i, C7466.adjugate i i ≠ 0) := by
  intro h
  have := certificate7466
  rw [h.1] at this
  norm_num at this
def C7467 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7467 : C7467.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7467 : ¬ (C7467.det = 0 ∧ ∀ i, C7467.adjugate i i ≠ 0) := by
  intro h
  have := certificate7467
  rw [h.1] at this
  norm_num at this
def C7468 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7468 : C7468.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7468 : ¬ (C7468.det = 0 ∧ ∀ i, C7468.adjugate i i ≠ 0) := by
  intro h
  have := certificate7468
  rw [h.1] at this
  norm_num at this
def C7469 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7469 : C7469.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7469 : ¬ (C7469.det = 0 ∧ ∀ i, C7469.adjugate i i ≠ 0) := by
  intro h
  have := certificate7469
  rw [h.1] at this
  norm_num at this
def C7470 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7470 : C7470.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7470 : ¬ (C7470.det = 0 ∧ ∀ i, C7470.adjugate i i ≠ 0) := by
  intro h
  have := certificate7470
  rw [h.1] at this
  norm_num at this
def C7471 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7471 : C7471.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7471 : ¬ (C7471.det = 0 ∧ ∀ i, C7471.adjugate i i ≠ 0) := by
  intro h
  have := certificate7471
  rw [h.1] at this
  norm_num at this
def C7472 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7472 : C7472.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7472 : ¬ (C7472.det = 0 ∧ ∀ i, C7472.adjugate i i ≠ 0) := by
  intro h
  have := certificate7472
  rw [h.1] at this
  norm_num at this
def C7473 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7473 : C7473.det = (196 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7473 : ¬ (C7473.det = 0 ∧ ∀ i, C7473.adjugate i i ≠ 0) := by
  intro h
  have := certificate7473
  rw [h.1] at this
  norm_num at this
def C7474 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7474 : C7474.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7474 : ¬ (C7474.det = 0 ∧ ∀ i, C7474.adjugate i i ≠ 0) := by
  intro h
  have := certificate7474
  rw [h.1] at this
  norm_num at this
def C7475 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7475 : C7475.det = (100 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7475 : ¬ (C7475.det = 0 ∧ ∀ i, C7475.adjugate i i ≠ 0) := by
  intro h
  have := certificate7475
  rw [h.1] at this
  norm_num at this
def C7476 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7476 : C7476.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7476 : ¬ (C7476.det = 0 ∧ ∀ i, C7476.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7476
def C7477 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7477 : C7477.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7477 : ¬ (C7477.det = 0 ∧ ∀ i, C7477.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7477
def C7478 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7478 : C7478.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7478 : ¬ (C7478.det = 0 ∧ ∀ i, C7478.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7478
def C7479 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7479 : C7479.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7479 : ¬ (C7479.det = 0 ∧ ∀ i, C7479.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7479
def C7480 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7480 : C7480.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7480 : ¬ (C7480.det = 0 ∧ ∀ i, C7480.adjugate i i ≠ 0) := by
  intro h
  have := certificate7480
  rw [h.1] at this
  norm_num at this
def C7481 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7481 : C7481.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7481 : ¬ (C7481.det = 0 ∧ ∀ i, C7481.adjugate i i ≠ 0) := by
  intro h
  have := certificate7481
  rw [h.1] at this
  norm_num at this
def C7482 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7482 : C7482.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7482 : ¬ (C7482.det = 0 ∧ ∀ i, C7482.adjugate i i ≠ 0) := by
  intro h
  have := certificate7482
  rw [h.1] at this
  norm_num at this
def C7483 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7483 : C7483.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7483 : ¬ (C7483.det = 0 ∧ ∀ i, C7483.adjugate i i ≠ 0) := by
  intro h
  have := certificate7483
  rw [h.1] at this
  norm_num at this
def C7484 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7484 : C7484.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7484 : ¬ (C7484.det = 0 ∧ ∀ i, C7484.adjugate i i ≠ 0) := by
  intro h
  have := certificate7484
  rw [h.1] at this
  norm_num at this
def C7485 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7485 : C7485.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7485 : ¬ (C7485.det = 0 ∧ ∀ i, C7485.adjugate i i ≠ 0) := by
  intro h
  have := certificate7485
  rw [h.1] at this
  norm_num at this
def C7486 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7486 : C7486.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7486 : ¬ (C7486.det = 0 ∧ ∀ i, C7486.adjugate i i ≠ 0) := by
  intro h
  have := certificate7486
  rw [h.1] at this
  norm_num at this
def C7487 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7487 : C7487.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7487 : ¬ (C7487.det = 0 ∧ ∀ i, C7487.adjugate i i ≠ 0) := by
  intro h
  have := certificate7487
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0233
