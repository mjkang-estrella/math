import VerifiedDet
namespace Nut8.NewCertificates0107
def C3424 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3424 : C3424.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3424 : ¬ (C3424.det = 0 ∧ ∀ i, C3424.adjugate i i ≠ 0) := by
  intro h
  have := certificate3424
  rw [h.1] at this
  norm_num at this
def C3425 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3425 : C3425.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3425 : ¬ (C3425.det = 0 ∧ ∀ i, C3425.adjugate i i ≠ 0) := by
  intro h
  have := certificate3425
  rw [h.1] at this
  norm_num at this
def C3426 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3426 : C3426.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3426 : ¬ (C3426.det = 0 ∧ ∀ i, C3426.adjugate i i ≠ 0) := by
  intro h
  have := certificate3426
  rw [h.1] at this
  norm_num at this
def C3427 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3427 : C3427.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3427 : ¬ (C3427.det = 0 ∧ ∀ i, C3427.adjugate i i ≠ 0) := by
  intro h
  have := certificate3427
  rw [h.1] at this
  norm_num at this
def C3428 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3428 : C3428.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3428 : ¬ (C3428.det = 0 ∧ ∀ i, C3428.adjugate i i ≠ 0) := by
  intro h
  have := certificate3428
  rw [h.1] at this
  norm_num at this
def C3429 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3429 : C3429.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3429 : ¬ (C3429.det = 0 ∧ ∀ i, C3429.adjugate i i ≠ 0) := by
  intro h
  have := certificate3429
  rw [h.1] at this
  norm_num at this
def C3430 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3430 : C3430.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3430 : ¬ (C3430.det = 0 ∧ ∀ i, C3430.adjugate i i ≠ 0) := by
  intro h
  have := certificate3430
  rw [h.1] at this
  norm_num at this
def C3431 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3431 : C3431.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3431 : ¬ (C3431.det = 0 ∧ ∀ i, C3431.adjugate i i ≠ 0) := by
  intro h
  have := certificate3431
  rw [h.1] at this
  norm_num at this
def C3432 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3432 : C3432.det = (39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3432 : ¬ (C3432.det = 0 ∧ ∀ i, C3432.adjugate i i ≠ 0) := by
  intro h
  have := certificate3432
  rw [h.1] at this
  norm_num at this
def C3433 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3433 : C3433.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3433 : ¬ (C3433.det = 0 ∧ ∀ i, C3433.adjugate i i ≠ 0) := by
  intro h
  have := certificate3433
  rw [h.1] at this
  norm_num at this
def C3434 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3434 : C3434.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3434 : ¬ (C3434.det = 0 ∧ ∀ i, C3434.adjugate i i ≠ 0) := by
  intro h
  have := certificate3434
  rw [h.1] at this
  norm_num at this
def C3435 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3435 : C3435.det = (39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3435 : ¬ (C3435.det = 0 ∧ ∀ i, C3435.adjugate i i ≠ 0) := by
  intro h
  have := certificate3435
  rw [h.1] at this
  norm_num at this
def C3436 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3436 : C3436.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3436 : ¬ (C3436.det = 0 ∧ ∀ i, C3436.adjugate i i ≠ 0) := by
  intro h
  have := certificate3436
  rw [h.1] at this
  norm_num at this
def C3437 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3437 : C3437.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3437 : ¬ (C3437.det = 0 ∧ ∀ i, C3437.adjugate i i ≠ 0) := by
  intro h
  have := certificate3437
  rw [h.1] at this
  norm_num at this
def C3438 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3438 : C3438.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3438 : ¬ (C3438.det = 0 ∧ ∀ i, C3438.adjugate i i ≠ 0) := by
  intro h
  have := certificate3438
  rw [h.1] at this
  norm_num at this
def C3439 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3439 : C3439.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3439 : ¬ (C3439.det = 0 ∧ ∀ i, C3439.adjugate i i ≠ 0) := by
  intro h
  have := certificate3439
  rw [h.1] at this
  norm_num at this
def C3440 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3440 : C3440.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3440 : ¬ (C3440.det = 0 ∧ ∀ i, C3440.adjugate i i ≠ 0) := by
  intro h
  have := certificate3440
  rw [h.1] at this
  norm_num at this
def C3441 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3441 : C3441.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3441 : ¬ (C3441.det = 0 ∧ ∀ i, C3441.adjugate i i ≠ 0) := by
  intro h
  have := certificate3441
  rw [h.1] at this
  norm_num at this
def C3442 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3442 : C3442.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3442 : ¬ (C3442.det = 0 ∧ ∀ i, C3442.adjugate i i ≠ 0) := by
  intro h
  have := certificate3442
  rw [h.1] at this
  norm_num at this
def C3443 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3443 : C3443.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3443 : ¬ (C3443.det = 0 ∧ ∀ i, C3443.adjugate i i ≠ 0) := by
  intro h
  have := certificate3443
  rw [h.1] at this
  norm_num at this
def C3444 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3444 : C3444.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3444 : ¬ (C3444.det = 0 ∧ ∀ i, C3444.adjugate i i ≠ 0) := by
  intro h
  have := certificate3444
  rw [h.1] at this
  norm_num at this
def C3445 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3445 : C3445.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3445 : ¬ (C3445.det = 0 ∧ ∀ i, C3445.adjugate i i ≠ 0) := by
  intro h
  have := certificate3445
  rw [h.1] at this
  norm_num at this
def C3446 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3446 : C3446.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3446 : ¬ (C3446.det = 0 ∧ ∀ i, C3446.adjugate i i ≠ 0) := by
  intro h
  have := certificate3446
  rw [h.1] at this
  norm_num at this
def C3447 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3447 : C3447.det = (38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3447 : ¬ (C3447.det = 0 ∧ ∀ i, C3447.adjugate i i ≠ 0) := by
  intro h
  have := certificate3447
  rw [h.1] at this
  norm_num at this
def C3448 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3448 : C3448.det = (38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3448 : ¬ (C3448.det = 0 ∧ ∀ i, C3448.adjugate i i ≠ 0) := by
  intro h
  have := certificate3448
  rw [h.1] at this
  norm_num at this
def C3449 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3449 : C3449.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3449 : ¬ (C3449.det = 0 ∧ ∀ i, C3449.adjugate i i ≠ 0) := by
  intro h
  have := certificate3449
  rw [h.1] at this
  norm_num at this
def C3450 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3450 : C3450.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3450 : ¬ (C3450.det = 0 ∧ ∀ i, C3450.adjugate i i ≠ 0) := by
  intro h
  have := certificate3450
  rw [h.1] at this
  norm_num at this
def C3451 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3451 : C3451.det = (86 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3451 : ¬ (C3451.det = 0 ∧ ∀ i, C3451.adjugate i i ≠ 0) := by
  intro h
  have := certificate3451
  rw [h.1] at this
  norm_num at this
def C3452 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3452 : C3452.det = (86 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3452 : ¬ (C3452.det = 0 ∧ ∀ i, C3452.adjugate i i ≠ 0) := by
  intro h
  have := certificate3452
  rw [h.1] at this
  norm_num at this
def C3453 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3453 : C3453.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3453 : ¬ (C3453.det = 0 ∧ ∀ i, C3453.adjugate i i ≠ 0) := by
  intro h
  have := certificate3453
  rw [h.1] at this
  norm_num at this
def C3454 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3454 : C3454.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3454 : ¬ (C3454.det = 0 ∧ ∀ i, C3454.adjugate i i ≠ 0) := by
  intro h
  have := certificate3454
  rw [h.1] at this
  norm_num at this
def C3455 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3455 : C3455.det = (38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3455 : ¬ (C3455.det = 0 ∧ ∀ i, C3455.adjugate i i ≠ 0) := by
  intro h
  have := certificate3455
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0107
