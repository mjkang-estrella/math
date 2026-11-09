import VerifiedDet
namespace Nut8.NewCertificates0106
def C3392 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3392 : C3392.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3392 : ¬ (C3392.det = 0 ∧ ∀ i, C3392.adjugate i i ≠ 0) := by
  intro h
  have := certificate3392
  rw [h.1] at this
  norm_num at this
def C3393 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3393 : C3393.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3393 : ¬ (C3393.det = 0 ∧ ∀ i, C3393.adjugate i i ≠ 0) := by
  intro h
  have := certificate3393
  rw [h.1] at this
  norm_num at this
def C3394 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3394 : C3394.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3394 : ¬ (C3394.det = 0 ∧ ∀ i, C3394.adjugate i i ≠ 0) := by
  intro h
  have := certificate3394
  rw [h.1] at this
  norm_num at this
def C3395 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3395 : C3395.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3395 : ¬ (C3395.det = 0 ∧ ∀ i, C3395.adjugate i i ≠ 0) := by
  intro h
  have := certificate3395
  rw [h.1] at this
  norm_num at this
def C3396 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3396 : C3396.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3396 : ¬ (C3396.det = 0 ∧ ∀ i, C3396.adjugate i i ≠ 0) := by
  intro h
  have := certificate3396
  rw [h.1] at this
  norm_num at this
def C3397 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3397 : C3397.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3397 : ¬ (C3397.det = 0 ∧ ∀ i, C3397.adjugate i i ≠ 0) := by
  intro h
  have := certificate3397
  rw [h.1] at this
  norm_num at this
def C3398 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3398 : C3398.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3398 : ¬ (C3398.det = 0 ∧ ∀ i, C3398.adjugate i i ≠ 0) := by
  intro h
  have := certificate3398
  rw [h.1] at this
  norm_num at this
def C3399 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3399 : C3399.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3399 : ¬ (C3399.det = 0 ∧ ∀ i, C3399.adjugate i i ≠ 0) := by
  intro h
  have := certificate3399
  rw [h.1] at this
  norm_num at this
def C3400 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3400 : C3400.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3400 : ¬ (C3400.det = 0 ∧ ∀ i, C3400.adjugate i i ≠ 0) := by
  intro h
  have := certificate3400
  rw [h.1] at this
  norm_num at this
def C3401 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3401 : C3401.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3401 : ¬ (C3401.det = 0 ∧ ∀ i, C3401.adjugate i i ≠ 0) := by
  intro h
  have := certificate3401
  rw [h.1] at this
  norm_num at this
def C3402 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3402 : C3402.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3402 : ¬ (C3402.det = 0 ∧ ∀ i, C3402.adjugate i i ≠ 0) := by
  intro h
  have := certificate3402
  rw [h.1] at this
  norm_num at this
def C3403 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3403 : C3403.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3403 : ¬ (C3403.det = 0 ∧ ∀ i, C3403.adjugate i i ≠ 0) := by
  intro h
  have := certificate3403
  rw [h.1] at this
  norm_num at this
def C3404 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3404 : C3404.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3404 : ¬ (C3404.det = 0 ∧ ∀ i, C3404.adjugate i i ≠ 0) := by
  intro h
  have := certificate3404
  rw [h.1] at this
  norm_num at this
def C3405 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3405 : C3405.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3405 : ¬ (C3405.det = 0 ∧ ∀ i, C3405.adjugate i i ≠ 0) := by
  intro h
  have := certificate3405
  rw [h.1] at this
  norm_num at this
def C3406 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3406 : C3406.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3406 : ¬ (C3406.det = 0 ∧ ∀ i, C3406.adjugate i i ≠ 0) := by
  intro h
  have := certificate3406
  rw [h.1] at this
  norm_num at this
def C3407 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3407 : C3407.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3407 : ¬ (C3407.det = 0 ∧ ∀ i, C3407.adjugate i i ≠ 0) := by
  intro h
  have := certificate3407
  rw [h.1] at this
  norm_num at this
def C3408 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3408 : C3408.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3408 : ¬ (C3408.det = 0 ∧ ∀ i, C3408.adjugate i i ≠ 0) := by
  intro h
  have := certificate3408
  rw [h.1] at this
  norm_num at this
def C3409 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3409 : C3409.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3409 : ¬ (C3409.det = 0 ∧ ∀ i, C3409.adjugate i i ≠ 0) := by
  intro h
  have := certificate3409
  rw [h.1] at this
  norm_num at this
def C3410 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3410 : C3410.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3410 : ¬ (C3410.det = 0 ∧ ∀ i, C3410.adjugate i i ≠ 0) := by
  intro h
  have := certificate3410
  rw [h.1] at this
  norm_num at this
def C3411 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3411 : C3411.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3411 : ¬ (C3411.det = 0 ∧ ∀ i, C3411.adjugate i i ≠ 0) := by
  intro h
  have := certificate3411
  rw [h.1] at this
  norm_num at this
def C3412 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3412 : C3412.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3412 : ¬ (C3412.det = 0 ∧ ∀ i, C3412.adjugate i i ≠ 0) := by
  intro h
  have := certificate3412
  rw [h.1] at this
  norm_num at this
def C3413 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3413 : C3413.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3413 : ¬ (C3413.det = 0 ∧ ∀ i, C3413.adjugate i i ≠ 0) := by
  intro h
  have := certificate3413
  rw [h.1] at this
  norm_num at this
def C3414 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3414 : C3414.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3414 : ¬ (C3414.det = 0 ∧ ∀ i, C3414.adjugate i i ≠ 0) := by
  intro h
  have := certificate3414
  rw [h.1] at this
  norm_num at this
def C3415 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3415 : C3415.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3415 : ¬ (C3415.det = 0 ∧ ∀ i, C3415.adjugate i i ≠ 0) := by
  intro h
  have := certificate3415
  rw [h.1] at this
  norm_num at this
def C3416 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3416 : C3416.det = (39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3416 : ¬ (C3416.det = 0 ∧ ∀ i, C3416.adjugate i i ≠ 0) := by
  intro h
  have := certificate3416
  rw [h.1] at this
  norm_num at this
def C3417 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3417 : C3417.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3417 : ¬ (C3417.det = 0 ∧ ∀ i, C3417.adjugate i i ≠ 0) := by
  intro h
  have := certificate3417
  rw [h.1] at this
  norm_num at this
def C3418 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3418 : C3418.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3418 : ¬ (C3418.det = 0 ∧ ∀ i, C3418.adjugate i i ≠ 0) := by
  intro h
  have := certificate3418
  rw [h.1] at this
  norm_num at this
def C3419 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3419 : C3419.det = (39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3419 : ¬ (C3419.det = 0 ∧ ∀ i, C3419.adjugate i i ≠ 0) := by
  intro h
  have := certificate3419
  rw [h.1] at this
  norm_num at this
def C3420 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3420 : C3420.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3420 : ¬ (C3420.det = 0 ∧ ∀ i, C3420.adjugate i i ≠ 0) := by
  intro h
  have := certificate3420
  rw [h.1] at this
  norm_num at this
def C3421 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3421 : C3421.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3421 : ¬ (C3421.det = 0 ∧ ∀ i, C3421.adjugate i i ≠ 0) := by
  intro h
  have := certificate3421
  rw [h.1] at this
  norm_num at this
def C3422 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3422 : C3422.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3422 : ¬ (C3422.det = 0 ∧ ∀ i, C3422.adjugate i i ≠ 0) := by
  intro h
  have := certificate3422
  rw [h.1] at this
  norm_num at this
def C3423 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3423 : C3423.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3423 : ¬ (C3423.det = 0 ∧ ∀ i, C3423.adjugate i i ≠ 0) := by
  intro h
  have := certificate3423
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0106
