import VerifiedDet
namespace Nut8.NewCertificates0232
def C7424 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7424 : C7424.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7424 : ¬ (C7424.det = 0 ∧ ∀ i, C7424.adjugate i i ≠ 0) := by
  intro h
  have := certificate7424
  rw [h.1] at this
  norm_num at this
def C7425 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7425 : C7425.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7425 : ¬ (C7425.det = 0 ∧ ∀ i, C7425.adjugate i i ≠ 0) := by
  intro h
  have := certificate7425
  rw [h.1] at this
  norm_num at this
def C7426 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7426 : C7426.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7426 : ¬ (C7426.det = 0 ∧ ∀ i, C7426.adjugate i i ≠ 0) := by
  intro h
  have := certificate7426
  rw [h.1] at this
  norm_num at this
def C7427 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7427 : C7427.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7427 : ¬ (C7427.det = 0 ∧ ∀ i, C7427.adjugate i i ≠ 0) := by
  intro h
  have := certificate7427
  rw [h.1] at this
  norm_num at this
def C7428 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7428 : C7428.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7428 : ¬ (C7428.det = 0 ∧ ∀ i, C7428.adjugate i i ≠ 0) := by
  intro h
  have := certificate7428
  rw [h.1] at this
  norm_num at this
def C7429 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7429 : C7429.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7429 : ¬ (C7429.det = 0 ∧ ∀ i, C7429.adjugate i i ≠ 0) := by
  intro h
  have := certificate7429
  rw [h.1] at this
  norm_num at this
def C7430 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7430 : C7430.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7430 : ¬ (C7430.det = 0 ∧ ∀ i, C7430.adjugate i i ≠ 0) := by
  intro h
  have := certificate7430
  rw [h.1] at this
  norm_num at this
def C7431 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7431 : C7431.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7431 : ¬ (C7431.det = 0 ∧ ∀ i, C7431.adjugate i i ≠ 0) := by
  intro h
  have := certificate7431
  rw [h.1] at this
  norm_num at this
def C7432 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7432 : C7432.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7432 : ¬ (C7432.det = 0 ∧ ∀ i, C7432.adjugate i i ≠ 0) := by
  intro h
  have := certificate7432
  rw [h.1] at this
  norm_num at this
def C7433 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7433 : C7433.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7433 : ¬ (C7433.det = 0 ∧ ∀ i, C7433.adjugate i i ≠ 0) := by
  intro h
  have := certificate7433
  rw [h.1] at this
  norm_num at this
def C7434 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7434 : C7434.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7434 : ¬ (C7434.det = 0 ∧ ∀ i, C7434.adjugate i i ≠ 0) := by
  intro h
  have := certificate7434
  rw [h.1] at this
  norm_num at this
def C7435 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7435 : C7435.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7435 : ¬ (C7435.det = 0 ∧ ∀ i, C7435.adjugate i i ≠ 0) := by
  intro h
  have := certificate7435
  rw [h.1] at this
  norm_num at this
def C7436 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7436 : C7436.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7436 : ¬ (C7436.det = 0 ∧ ∀ i, C7436.adjugate i i ≠ 0) := by
  intro h
  have := certificate7436
  rw [h.1] at this
  norm_num at this
def C7437 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7437 : C7437.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7437 : ¬ (C7437.det = 0 ∧ ∀ i, C7437.adjugate i i ≠ 0) := by
  intro h
  have := certificate7437
  rw [h.1] at this
  norm_num at this
def C7438 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7438 : C7438.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7438 : ¬ (C7438.det = 0 ∧ ∀ i, C7438.adjugate i i ≠ 0) := by
  intro h
  have := certificate7438
  rw [h.1] at this
  norm_num at this
def C7439 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7439 : C7439.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7439 : ¬ (C7439.det = 0 ∧ ∀ i, C7439.adjugate i i ≠ 0) := by
  intro h
  have := certificate7439
  rw [h.1] at this
  norm_num at this
def C7440 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7440 : C7440.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7440 : ¬ (C7440.det = 0 ∧ ∀ i, C7440.adjugate i i ≠ 0) := by
  intro h
  have := certificate7440
  rw [h.1] at this
  norm_num at this
def C7441 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7441 : C7441.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7441 : ¬ (C7441.det = 0 ∧ ∀ i, C7441.adjugate i i ≠ 0) := by
  intro h
  have := certificate7441
  rw [h.1] at this
  norm_num at this
def C7442 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7442 : C7442.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7442 : ¬ (C7442.det = 0 ∧ ∀ i, C7442.adjugate i i ≠ 0) := by
  intro h
  have := certificate7442
  rw [h.1] at this
  norm_num at this
def C7443 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7443 : C7443.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7443 : ¬ (C7443.det = 0 ∧ ∀ i, C7443.adjugate i i ≠ 0) := by
  intro h
  have := certificate7443
  rw [h.1] at this
  norm_num at this
def C7444 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7444 : C7444.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7444 : ¬ (C7444.det = 0 ∧ ∀ i, C7444.adjugate i i ≠ 0) := by
  intro h
  have := certificate7444
  rw [h.1] at this
  norm_num at this
def C7445 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7445 : C7445.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7445 : ¬ (C7445.det = 0 ∧ ∀ i, C7445.adjugate i i ≠ 0) := by
  intro h
  have := certificate7445
  rw [h.1] at this
  norm_num at this
def C7446 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7446 : C7446.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7446 : ¬ (C7446.det = 0 ∧ ∀ i, C7446.adjugate i i ≠ 0) := by
  intro h
  have := certificate7446
  rw [h.1] at this
  norm_num at this
def C7447 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7447 : C7447.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7447 : ¬ (C7447.det = 0 ∧ ∀ i, C7447.adjugate i i ≠ 0) := by
  intro h
  have := certificate7447
  rw [h.1] at this
  norm_num at this
def C7448 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7448 : C7448.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7448 : ¬ (C7448.det = 0 ∧ ∀ i, C7448.adjugate i i ≠ 0) := by
  intro h
  have := certificate7448
  rw [h.1] at this
  norm_num at this
def C7449 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7449 : C7449.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7449 : ¬ (C7449.det = 0 ∧ ∀ i, C7449.adjugate i i ≠ 0) := by
  intro h
  have := certificate7449
  rw [h.1] at this
  norm_num at this
def C7450 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7450 : C7450.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7450 : ¬ (C7450.det = 0 ∧ ∀ i, C7450.adjugate i i ≠ 0) := by
  intro h
  have := certificate7450
  rw [h.1] at this
  norm_num at this
def C7451 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7451 : C7451.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7451 : ¬ (C7451.det = 0 ∧ ∀ i, C7451.adjugate i i ≠ 0) := by
  intro h
  have := certificate7451
  rw [h.1] at this
  norm_num at this
def C7452 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7452 : C7452.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7452 : ¬ (C7452.det = 0 ∧ ∀ i, C7452.adjugate i i ≠ 0) := by
  intro h
  have := certificate7452
  rw [h.1] at this
  norm_num at this
def C7453 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7453 : C7453.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7453 : ¬ (C7453.det = 0 ∧ ∀ i, C7453.adjugate i i ≠ 0) := by
  intro h
  have := certificate7453
  rw [h.1] at this
  norm_num at this
def C7454 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7454 : C7454.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7454 : ¬ (C7454.det = 0 ∧ ∀ i, C7454.adjugate i i ≠ 0) := by
  intro h
  have := certificate7454
  rw [h.1] at this
  norm_num at this
def C7455 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7455 : C7455.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7455 : ¬ (C7455.det = 0 ∧ ∀ i, C7455.adjugate i i ≠ 0) := by
  intro h
  have := certificate7455
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0232
