import VerifiedDet
namespace Nut8.NewCertificates0104
def C3328 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3328 : C3328.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3328 : ¬ (C3328.det = 0 ∧ ∀ i, C3328.adjugate i i ≠ 0) := by
  intro h
  have := certificate3328
  rw [h.1] at this
  norm_num at this
def C3329 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3329 : C3329.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3329 : ¬ (C3329.det = 0 ∧ ∀ i, C3329.adjugate i i ≠ 0) := by
  intro h
  have := certificate3329
  rw [h.1] at this
  norm_num at this
def C3330 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3330 : C3330.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3330 : ¬ (C3330.det = 0 ∧ ∀ i, C3330.adjugate i i ≠ 0) := by
  intro h
  have := certificate3330
  rw [h.1] at this
  norm_num at this
def C3331 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3331 : C3331.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3331 : ¬ (C3331.det = 0 ∧ ∀ i, C3331.adjugate i i ≠ 0) := by
  intro h
  have := certificate3331
  rw [h.1] at this
  norm_num at this
def C3332 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3332 : C3332.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3332 : ¬ (C3332.det = 0 ∧ ∀ i, C3332.adjugate i i ≠ 0) := by
  intro h
  have := certificate3332
  rw [h.1] at this
  norm_num at this
def C3333 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3333 : C3333.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3333 : ¬ (C3333.det = 0 ∧ ∀ i, C3333.adjugate i i ≠ 0) := by
  intro h
  have := certificate3333
  rw [h.1] at this
  norm_num at this
def C3334 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3334 : C3334.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3334 : ¬ (C3334.det = 0 ∧ ∀ i, C3334.adjugate i i ≠ 0) := by
  intro h
  have := certificate3334
  rw [h.1] at this
  norm_num at this
def C3335 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3335 : C3335.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3335 : ¬ (C3335.det = 0 ∧ ∀ i, C3335.adjugate i i ≠ 0) := by
  intro h
  have := certificate3335
  rw [h.1] at this
  norm_num at this
def C3336 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3336 : C3336.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3336 : ¬ (C3336.det = 0 ∧ ∀ i, C3336.adjugate i i ≠ 0) := by
  intro h
  have := certificate3336
  rw [h.1] at this
  norm_num at this
def C3337 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3337 : C3337.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3337 : ¬ (C3337.det = 0 ∧ ∀ i, C3337.adjugate i i ≠ 0) := by
  intro h
  have := certificate3337
  rw [h.1] at this
  norm_num at this
def C3338 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3338 : C3338.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3338 : ¬ (C3338.det = 0 ∧ ∀ i, C3338.adjugate i i ≠ 0) := by
  intro h
  have := certificate3338
  rw [h.1] at this
  norm_num at this
def C3339 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3339 : C3339.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3339 : ¬ (C3339.det = 0 ∧ ∀ i, C3339.adjugate i i ≠ 0) := by
  intro h
  have := certificate3339
  rw [h.1] at this
  norm_num at this
def C3340 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3340 : C3340.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3340 : ¬ (C3340.det = 0 ∧ ∀ i, C3340.adjugate i i ≠ 0) := by
  intro h
  have := certificate3340
  rw [h.1] at this
  norm_num at this
def C3341 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3341 : C3341.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3341 : ¬ (C3341.det = 0 ∧ ∀ i, C3341.adjugate i i ≠ 0) := by
  intro h
  have := certificate3341
  rw [h.1] at this
  norm_num at this
def C3342 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3342 : C3342.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3342 : ¬ (C3342.det = 0 ∧ ∀ i, C3342.adjugate i i ≠ 0) := by
  intro h
  have := certificate3342
  rw [h.1] at this
  norm_num at this
def C3343 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3343 : C3343.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3343 : ¬ (C3343.det = 0 ∧ ∀ i, C3343.adjugate i i ≠ 0) := by
  intro h
  have := certificate3343
  rw [h.1] at this
  norm_num at this
def C3344 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3344 : C3344.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3344 : ¬ (C3344.det = 0 ∧ ∀ i, C3344.adjugate i i ≠ 0) := by
  intro h
  have := certificate3344
  rw [h.1] at this
  norm_num at this
def C3345 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3345 : C3345.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3345 : ¬ (C3345.det = 0 ∧ ∀ i, C3345.adjugate i i ≠ 0) := by
  intro h
  have := certificate3345
  rw [h.1] at this
  norm_num at this
def C3346 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3346 : C3346.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3346 : ¬ (C3346.det = 0 ∧ ∀ i, C3346.adjugate i i ≠ 0) := by
  intro h
  have := certificate3346
  rw [h.1] at this
  norm_num at this
def C3347 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3347 : C3347.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3347 : ¬ (C3347.det = 0 ∧ ∀ i, C3347.adjugate i i ≠ 0) := by
  intro h
  have := certificate3347
  rw [h.1] at this
  norm_num at this
def C3348 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3348 : C3348.det = (43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3348 : ¬ (C3348.det = 0 ∧ ∀ i, C3348.adjugate i i ≠ 0) := by
  intro h
  have := certificate3348
  rw [h.1] at this
  norm_num at this
def C3349 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3349 : C3349.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3349 : ¬ (C3349.det = 0 ∧ ∀ i, C3349.adjugate i i ≠ 0) := by
  intro h
  have := certificate3349
  rw [h.1] at this
  norm_num at this
def C3350 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3350 : C3350.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3350 : ¬ (C3350.det = 0 ∧ ∀ i, C3350.adjugate i i ≠ 0) := by
  intro h
  have := certificate3350
  rw [h.1] at this
  norm_num at this
def C3351 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3351 : C3351.det = (43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3351 : ¬ (C3351.det = 0 ∧ ∀ i, C3351.adjugate i i ≠ 0) := by
  intro h
  have := certificate3351
  rw [h.1] at this
  norm_num at this
def C3352 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3352 : C3352.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3352 : ¬ (C3352.det = 0 ∧ ∀ i, C3352.adjugate i i ≠ 0) := by
  intro h
  have := certificate3352
  rw [h.1] at this
  norm_num at this
def C3353 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3353 : C3353.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3353 : ¬ (C3353.det = 0 ∧ ∀ i, C3353.adjugate i i ≠ 0) := by
  intro h
  have := certificate3353
  rw [h.1] at this
  norm_num at this
def C3354 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3354 : C3354.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3354 : ¬ (C3354.det = 0 ∧ ∀ i, C3354.adjugate i i ≠ 0) := by
  intro h
  have := certificate3354
  rw [h.1] at this
  norm_num at this
def C3355 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3355 : C3355.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3355 : ¬ (C3355.det = 0 ∧ ∀ i, C3355.adjugate i i ≠ 0) := by
  intro h
  have := certificate3355
  rw [h.1] at this
  norm_num at this
def C3356 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3356 : C3356.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3356 : ¬ (C3356.det = 0 ∧ ∀ i, C3356.adjugate i i ≠ 0) := by
  intro h
  have := certificate3356
  rw [h.1] at this
  norm_num at this
def C3357 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3357 : C3357.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3357 : ¬ (C3357.det = 0 ∧ ∀ i, C3357.adjugate i i ≠ 0) := by
  intro h
  have := certificate3357
  rw [h.1] at this
  norm_num at this
def C3358 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3358 : C3358.det = (-72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3358 : ¬ (C3358.det = 0 ∧ ∀ i, C3358.adjugate i i ≠ 0) := by
  intro h
  have := certificate3358
  rw [h.1] at this
  norm_num at this
def C3359 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3359 : C3359.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3359 : ¬ (C3359.det = 0 ∧ ∀ i, C3359.adjugate i i ≠ 0) := by
  intro h
  have := certificate3359
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0104
