import VerifiedDet
namespace Nut8.NewCertificates0105
def C3360 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3360 : C3360.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3360 : ¬ (C3360.det = 0 ∧ ∀ i, C3360.adjugate i i ≠ 0) := by
  intro h
  have := certificate3360
  rw [h.1] at this
  norm_num at this
def C3361 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3361 : C3361.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3361 : ¬ (C3361.det = 0 ∧ ∀ i, C3361.adjugate i i ≠ 0) := by
  intro h
  have := certificate3361
  rw [h.1] at this
  norm_num at this
def C3362 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3362 : C3362.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3362 : ¬ (C3362.det = 0 ∧ ∀ i, C3362.adjugate i i ≠ 0) := by
  intro h
  have := certificate3362
  rw [h.1] at this
  norm_num at this
def C3363 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3363 : C3363.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3363 : ¬ (C3363.det = 0 ∧ ∀ i, C3363.adjugate i i ≠ 0) := by
  intro h
  have := certificate3363
  rw [h.1] at this
  norm_num at this
def C3364 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3364 : C3364.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3364 : ¬ (C3364.det = 0 ∧ ∀ i, C3364.adjugate i i ≠ 0) := by
  intro h
  have := certificate3364
  rw [h.1] at this
  norm_num at this
def C3365 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3365 : C3365.det = (-72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3365 : ¬ (C3365.det = 0 ∧ ∀ i, C3365.adjugate i i ≠ 0) := by
  intro h
  have := certificate3365
  rw [h.1] at this
  norm_num at this
def C3366 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3366 : C3366.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3366 : ¬ (C3366.det = 0 ∧ ∀ i, C3366.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate3366
def C3367 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3367 : C3367.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3367 : ¬ (C3367.det = 0 ∧ ∀ i, C3367.adjugate i i ≠ 0) := by
  intro h
  have := certificate3367
  rw [h.1] at this
  norm_num at this
def C3368 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3368 : C3368.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3368 : ¬ (C3368.det = 0 ∧ ∀ i, C3368.adjugate i i ≠ 0) := by
  intro h
  have := certificate3368
  rw [h.1] at this
  norm_num at this
def C3369 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3369 : C3369.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3369 : ¬ (C3369.det = 0 ∧ ∀ i, C3369.adjugate i i ≠ 0) := by
  intro h
  have := certificate3369
  rw [h.1] at this
  norm_num at this
def C3370 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3370 : C3370.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3370 : ¬ (C3370.det = 0 ∧ ∀ i, C3370.adjugate i i ≠ 0) := by
  intro h
  have := certificate3370
  rw [h.1] at this
  norm_num at this
def C3371 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3371 : C3371.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3371 : ¬ (C3371.det = 0 ∧ ∀ i, C3371.adjugate i i ≠ 0) := by
  intro h
  have := certificate3371
  rw [h.1] at this
  norm_num at this
def C3372 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3372 : C3372.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3372 : ¬ (C3372.det = 0 ∧ ∀ i, C3372.adjugate i i ≠ 0) := by
  intro h
  have := certificate3372
  rw [h.1] at this
  norm_num at this
def C3373 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3373 : C3373.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3373 : ¬ (C3373.det = 0 ∧ ∀ i, C3373.adjugate i i ≠ 0) := by
  intro h
  have := certificate3373
  rw [h.1] at this
  norm_num at this
def C3374 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3374 : C3374.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3374 : ¬ (C3374.det = 0 ∧ ∀ i, C3374.adjugate i i ≠ 0) := by
  intro h
  have := certificate3374
  rw [h.1] at this
  norm_num at this
def C3375 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3375 : C3375.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3375 : ¬ (C3375.det = 0 ∧ ∀ i, C3375.adjugate i i ≠ 0) := by
  intro h
  have := certificate3375
  rw [h.1] at this
  norm_num at this
def C3376 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3376 : C3376.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3376 : ¬ (C3376.det = 0 ∧ ∀ i, C3376.adjugate i i ≠ 0) := by
  intro h
  have := certificate3376
  rw [h.1] at this
  norm_num at this
def C3377 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3377 : C3377.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3377 : ¬ (C3377.det = 0 ∧ ∀ i, C3377.adjugate i i ≠ 0) := by
  intro h
  have := certificate3377
  rw [h.1] at this
  norm_num at this
def C3378 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3378 : C3378.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3378 : ¬ (C3378.det = 0 ∧ ∀ i, C3378.adjugate i i ≠ 0) := by
  intro h
  have := certificate3378
  rw [h.1] at this
  norm_num at this
def C3379 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3379 : C3379.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3379 : ¬ (C3379.det = 0 ∧ ∀ i, C3379.adjugate i i ≠ 0) := by
  intro h
  have := certificate3379
  rw [h.1] at this
  norm_num at this
def C3380 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3380 : C3380.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3380 : ¬ (C3380.det = 0 ∧ ∀ i, C3380.adjugate i i ≠ 0) := by
  intro h
  have := certificate3380
  rw [h.1] at this
  norm_num at this
def C3381 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3381 : C3381.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3381 : ¬ (C3381.det = 0 ∧ ∀ i, C3381.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate3381
def C3382 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3382 : C3382.det = (-54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3382 : ¬ (C3382.det = 0 ∧ ∀ i, C3382.adjugate i i ≠ 0) := by
  intro h
  have := certificate3382
  rw [h.1] at this
  norm_num at this
def C3383 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3383 : C3383.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3383 : ¬ (C3383.det = 0 ∧ ∀ i, C3383.adjugate i i ≠ 0) := by
  intro h
  have := certificate3383
  rw [h.1] at this
  norm_num at this
def C3384 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3384 : C3384.det = (78 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3384 : ¬ (C3384.det = 0 ∧ ∀ i, C3384.adjugate i i ≠ 0) := by
  intro h
  have := certificate3384
  rw [h.1] at this
  norm_num at this
def C3385 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3385 : C3385.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3385 : ¬ (C3385.det = 0 ∧ ∀ i, C3385.adjugate i i ≠ 0) := by
  intro h
  have := certificate3385
  rw [h.1] at this
  norm_num at this
def C3386 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3386 : C3386.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3386 : ¬ (C3386.det = 0 ∧ ∀ i, C3386.adjugate i i ≠ 0) := by
  intro h
  have := certificate3386
  rw [h.1] at this
  norm_num at this
def C3387 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3387 : C3387.det = (78 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3387 : ¬ (C3387.det = 0 ∧ ∀ i, C3387.adjugate i i ≠ 0) := by
  intro h
  have := certificate3387
  rw [h.1] at this
  norm_num at this
def C3388 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3388 : C3388.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3388 : ¬ (C3388.det = 0 ∧ ∀ i, C3388.adjugate i i ≠ 0) := by
  intro h
  have := certificate3388
  rw [h.1] at this
  norm_num at this
def C3389 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3389 : C3389.det = (-54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3389 : ¬ (C3389.det = 0 ∧ ∀ i, C3389.adjugate i i ≠ 0) := by
  intro h
  have := certificate3389
  rw [h.1] at this
  norm_num at this
def C3390 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3390 : C3390.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3390 : ¬ (C3390.det = 0 ∧ ∀ i, C3390.adjugate i i ≠ 0) := by
  intro h
  have := certificate3390
  rw [h.1] at this
  norm_num at this
def C3391 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3391 : C3391.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3391 : ¬ (C3391.det = 0 ∧ ∀ i, C3391.adjugate i i ≠ 0) := by
  intro h
  have := certificate3391
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0105
