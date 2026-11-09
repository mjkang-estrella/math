import VerifiedDet
namespace Nut8.NewCertificates0235
def C7520 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7520 : C7520.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7520 : ¬ (C7520.det = 0 ∧ ∀ i, C7520.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7520
def C7521 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7521 : C7521.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7521 : ¬ (C7521.det = 0 ∧ ∀ i, C7521.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7521
def C7522 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7522 : C7522.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7522 : ¬ (C7522.det = 0 ∧ ∀ i, C7522.adjugate i i ≠ 0) := by
  intro h
  have := certificate7522
  rw [h.1] at this
  norm_num at this
def C7523 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7523 : C7523.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7523 : ¬ (C7523.det = 0 ∧ ∀ i, C7523.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7523
def C7524 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate7524 : C7524.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7524 : ¬ (C7524.det = 0 ∧ ∀ i, C7524.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7524
def C7525 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate7525 : C7525.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7525 : ¬ (C7525.det = 0 ∧ ∀ i, C7525.adjugate i i ≠ 0) := by
  intro h
  have := certificate7525
  rw [h.1] at this
  norm_num at this
def C7526 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate7526 : C7526.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7526 : ¬ (C7526.det = 0 ∧ ∀ i, C7526.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7526
def C7527 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate7527 : C7527.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7527 : ¬ (C7527.det = 0 ∧ ∀ i, C7527.adjugate i i ≠ 0) := by
  intro h
  have := certificate7527
  rw [h.1] at this
  norm_num at this
def C7528 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate7528 : C7528.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7528 : ¬ (C7528.det = 0 ∧ ∀ i, C7528.adjugate i i ≠ 0) := by
  intro h
  have := certificate7528
  rw [h.1] at this
  norm_num at this
def C7529 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate7529 : C7529.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7529 : ¬ (C7529.det = 0 ∧ ∀ i, C7529.adjugate i i ≠ 0) := by
  intro h
  have := certificate7529
  rw [h.1] at this
  norm_num at this
def C7530 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate7530 : C7530.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7530 : ¬ (C7530.det = 0 ∧ ∀ i, C7530.adjugate i i ≠ 0) := by
  intro h
  have := certificate7530
  rw [h.1] at this
  norm_num at this
def C7531 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate7531 : C7531.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7531 : ¬ (C7531.det = 0 ∧ ∀ i, C7531.adjugate i i ≠ 0) := by
  intro h
  have := certificate7531
  rw [h.1] at this
  norm_num at this
def C7532 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate7532 : C7532.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7532 : ¬ (C7532.det = 0 ∧ ∀ i, C7532.adjugate i i ≠ 0) := by
  intro h
  have := certificate7532
  rw [h.1] at this
  norm_num at this
def C7533 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate7533 : C7533.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7533 : ¬ (C7533.det = 0 ∧ ∀ i, C7533.adjugate i i ≠ 0) := by
  intro h
  have := certificate7533
  rw [h.1] at this
  norm_num at this
def C7534 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate7534 : C7534.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7534 : ¬ (C7534.det = 0 ∧ ∀ i, C7534.adjugate i i ≠ 0) := by
  intro h
  have := certificate7534
  rw [h.1] at this
  norm_num at this
def C7535 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate7535 : C7535.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7535 : ¬ (C7535.det = 0 ∧ ∀ i, C7535.adjugate i i ≠ 0) := by
  intro h
  have := certificate7535
  rw [h.1] at this
  norm_num at this
def C7536 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate7536 : C7536.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7536 : ¬ (C7536.det = 0 ∧ ∀ i, C7536.adjugate i i ≠ 0) := by
  intro h
  have := certificate7536
  rw [h.1] at this
  norm_num at this
def C7537 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate7537 : C7537.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7537 : ¬ (C7537.det = 0 ∧ ∀ i, C7537.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7537
def C7538 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate7538 : C7538.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7538 : ¬ (C7538.det = 0 ∧ ∀ i, C7538.adjugate i i ≠ 0) := by
  intro h
  have := certificate7538
  rw [h.1] at this
  norm_num at this
def C7539 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate7539 : C7539.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7539 : ¬ (C7539.det = 0 ∧ ∀ i, C7539.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7539
def C7540 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7540 : C7540.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7540 : ¬ (C7540.det = 0 ∧ ∀ i, C7540.adjugate i i ≠ 0) := by
  intro h
  have := certificate7540
  rw [h.1] at this
  norm_num at this
def C7541 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7541 : C7541.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7541 : ¬ (C7541.det = 0 ∧ ∀ i, C7541.adjugate i i ≠ 0) := by
  intro h
  have := certificate7541
  rw [h.1] at this
  norm_num at this
def C7542 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7542 : C7542.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7542 : ¬ (C7542.det = 0 ∧ ∀ i, C7542.adjugate i i ≠ 0) := by
  intro h
  have := certificate7542
  rw [h.1] at this
  norm_num at this
def C7543 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7543 : C7543.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7543 : ¬ (C7543.det = 0 ∧ ∀ i, C7543.adjugate i i ≠ 0) := by
  intro h
  have := certificate7543
  rw [h.1] at this
  norm_num at this
def C7544 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7544 : C7544.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7544 : ¬ (C7544.det = 0 ∧ ∀ i, C7544.adjugate i i ≠ 0) := by
  intro h
  have := certificate7544
  rw [h.1] at this
  norm_num at this
def C7545 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7545 : C7545.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7545 : ¬ (C7545.det = 0 ∧ ∀ i, C7545.adjugate i i ≠ 0) := by
  intro h
  have := certificate7545
  rw [h.1] at this
  norm_num at this
def C7546 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7546 : C7546.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7546 : ¬ (C7546.det = 0 ∧ ∀ i, C7546.adjugate i i ≠ 0) := by
  intro h
  have := certificate7546
  rw [h.1] at this
  norm_num at this
def C7547 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7547 : C7547.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7547 : ¬ (C7547.det = 0 ∧ ∀ i, C7547.adjugate i i ≠ 0) := by
  intro h
  have := certificate7547
  rw [h.1] at this
  norm_num at this
def C7548 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7548 : C7548.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7548 : ¬ (C7548.det = 0 ∧ ∀ i, C7548.adjugate i i ≠ 0) := by
  intro h
  have := certificate7548
  rw [h.1] at this
  norm_num at this
def C7549 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7549 : C7549.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7549 : ¬ (C7549.det = 0 ∧ ∀ i, C7549.adjugate i i ≠ 0) := by
  intro h
  have := certificate7549
  rw [h.1] at this
  norm_num at this
def C7550 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7550 : C7550.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7550 : ¬ (C7550.det = 0 ∧ ∀ i, C7550.adjugate i i ≠ 0) := by
  intro h
  have := certificate7550
  rw [h.1] at this
  norm_num at this
def C7551 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7551 : C7551.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7551 : ¬ (C7551.det = 0 ∧ ∀ i, C7551.adjugate i i ≠ 0) := by
  intro h
  have := certificate7551
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0235
