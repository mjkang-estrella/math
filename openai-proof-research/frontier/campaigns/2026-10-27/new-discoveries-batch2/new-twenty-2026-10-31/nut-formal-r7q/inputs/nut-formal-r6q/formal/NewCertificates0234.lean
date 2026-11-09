import VerifiedDet
namespace Nut8.NewCertificates0234
def C7488 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7488 : C7488.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7488 : ¬ (C7488.det = 0 ∧ ∀ i, C7488.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7488
def C7489 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7489 : C7489.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7489 : ¬ (C7489.det = 0 ∧ ∀ i, C7489.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7489
def C7490 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7490 : C7490.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7490 : ¬ (C7490.det = 0 ∧ ∀ i, C7490.adjugate i i ≠ 0) := by
  intro h
  have := certificate7490
  rw [h.1] at this
  norm_num at this
def C7491 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7491 : C7491.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7491 : ¬ (C7491.det = 0 ∧ ∀ i, C7491.adjugate i i ≠ 0) := by
  intro h
  have := certificate7491
  rw [h.1] at this
  norm_num at this
def C7492 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate7492 : C7492.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7492 : ¬ (C7492.det = 0 ∧ ∀ i, C7492.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7492
def C7493 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate7493 : C7493.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7493 : ¬ (C7493.det = 0 ∧ ∀ i, C7493.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7493
def C7494 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate7494 : C7494.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7494 : ¬ (C7494.det = 0 ∧ ∀ i, C7494.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7494
def C7495 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate7495 : C7495.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7495 : ¬ (C7495.det = 0 ∧ ∀ i, C7495.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7495
def C7496 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate7496 : C7496.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7496 : ¬ (C7496.det = 0 ∧ ∀ i, C7496.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7496
def C7497 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate7497 : C7497.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7497 : ¬ (C7497.det = 0 ∧ ∀ i, C7497.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7497
def C7498 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate7498 : C7498.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7498 : ¬ (C7498.det = 0 ∧ ∀ i, C7498.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7498
def C7499 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate7499 : C7499.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7499 : ¬ (C7499.det = 0 ∧ ∀ i, C7499.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7499
def C7500 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate7500 : C7500.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7500 : ¬ (C7500.det = 0 ∧ ∀ i, C7500.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7500
def C7501 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate7501 : C7501.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7501 : ¬ (C7501.det = 0 ∧ ∀ i, C7501.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7501
def C7502 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate7502 : C7502.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7502 : ¬ (C7502.det = 0 ∧ ∀ i, C7502.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7502
def C7503 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate7503 : C7503.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7503 : ¬ (C7503.det = 0 ∧ ∀ i, C7503.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7503
def C7504 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate7504 : C7504.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7504 : ¬ (C7504.det = 0 ∧ ∀ i, C7504.adjugate i i ≠ 0) := by
  intro h
  have := certificate7504
  rw [h.1] at this
  norm_num at this
def C7505 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate7505 : C7505.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7505 : ¬ (C7505.det = 0 ∧ ∀ i, C7505.adjugate i i ≠ 0) := by
  intro h
  have := certificate7505
  rw [h.1] at this
  norm_num at this
def C7506 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate7506 : C7506.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7506 : ¬ (C7506.det = 0 ∧ ∀ i, C7506.adjugate i i ≠ 0) := by
  intro h
  have := certificate7506
  rw [h.1] at this
  norm_num at this
def C7507 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate7507 : C7507.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7507 : ¬ (C7507.det = 0 ∧ ∀ i, C7507.adjugate i i ≠ 0) := by
  intro h
  have := certificate7507
  rw [h.1] at this
  norm_num at this
def C7508 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7508 : C7508.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7508 : ¬ (C7508.det = 0 ∧ ∀ i, C7508.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7508
def C7509 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7509 : C7509.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7509 : ¬ (C7509.det = 0 ∧ ∀ i, C7509.adjugate i i ≠ 0) := by
  intro h
  have := certificate7509
  rw [h.1] at this
  norm_num at this
def C7510 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7510 : C7510.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7510 : ¬ (C7510.det = 0 ∧ ∀ i, C7510.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7510
def C7511 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7511 : C7511.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7511 : ¬ (C7511.det = 0 ∧ ∀ i, C7511.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7511
def C7512 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7512 : C7512.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7512 : ¬ (C7512.det = 0 ∧ ∀ i, C7512.adjugate i i ≠ 0) := by
  intro h
  have := certificate7512
  rw [h.1] at this
  norm_num at this
def C7513 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7513 : C7513.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7513 : ¬ (C7513.det = 0 ∧ ∀ i, C7513.adjugate i i ≠ 0) := by
  intro h
  have := certificate7513
  rw [h.1] at this
  norm_num at this
def C7514 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7514 : C7514.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7514 : ¬ (C7514.det = 0 ∧ ∀ i, C7514.adjugate i i ≠ 0) := by
  intro h
  have := certificate7514
  rw [h.1] at this
  norm_num at this
def C7515 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7515 : C7515.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7515 : ¬ (C7515.det = 0 ∧ ∀ i, C7515.adjugate i i ≠ 0) := by
  intro h
  have := certificate7515
  rw [h.1] at this
  norm_num at this
def C7516 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7516 : C7516.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7516 : ¬ (C7516.det = 0 ∧ ∀ i, C7516.adjugate i i ≠ 0) := by
  intro h
  have := certificate7516
  rw [h.1] at this
  norm_num at this
def C7517 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7517 : C7517.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7517 : ¬ (C7517.det = 0 ∧ ∀ i, C7517.adjugate i i ≠ 0) := by
  intro h
  have := certificate7517
  rw [h.1] at this
  norm_num at this
def C7518 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7518 : C7518.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7518 : ¬ (C7518.det = 0 ∧ ∀ i, C7518.adjugate i i ≠ 0) := by
  intro h
  have := certificate7518
  rw [h.1] at this
  norm_num at this
def C7519 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7519 : C7519.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7519 : ¬ (C7519.det = 0 ∧ ∀ i, C7519.adjugate i i ≠ 0) := by
  intro h
  have := certificate7519
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0234
