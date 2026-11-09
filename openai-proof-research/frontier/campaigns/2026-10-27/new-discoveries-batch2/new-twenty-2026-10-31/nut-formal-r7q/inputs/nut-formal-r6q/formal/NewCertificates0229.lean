import VerifiedDet
namespace Nut8.NewCertificates0229
def C7328 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7328 : C7328.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7328 : ¬ (C7328.det = 0 ∧ ∀ i, C7328.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7328
def C7329 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7329 : C7329.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7329 : ¬ (C7329.det = 0 ∧ ∀ i, C7329.adjugate i i ≠ 0) := by
  intro h
  have := certificate7329
  rw [h.1] at this
  norm_num at this
def C7330 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7330 : C7330.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7330 : ¬ (C7330.det = 0 ∧ ∀ i, C7330.adjugate i i ≠ 0) := by
  intro h
  have := certificate7330
  rw [h.1] at this
  norm_num at this
def C7331 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7331 : C7331.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7331 : ¬ (C7331.det = 0 ∧ ∀ i, C7331.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7331
def C7332 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7332 : C7332.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7332 : ¬ (C7332.det = 0 ∧ ∀ i, C7332.adjugate i i ≠ 0) := by
  intro h
  have := certificate7332
  rw [h.1] at this
  norm_num at this
def C7333 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7333 : C7333.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7333 : ¬ (C7333.det = 0 ∧ ∀ i, C7333.adjugate i i ≠ 0) := by
  intro h
  have := certificate7333
  rw [h.1] at this
  norm_num at this
def C7334 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7334 : C7334.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7334 : ¬ (C7334.det = 0 ∧ ∀ i, C7334.adjugate i i ≠ 0) := by
  intro h
  have := certificate7334
  rw [h.1] at this
  norm_num at this
def C7335 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7335 : C7335.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7335 : ¬ (C7335.det = 0 ∧ ∀ i, C7335.adjugate i i ≠ 0) := by
  intro h
  have := certificate7335
  rw [h.1] at this
  norm_num at this
def C7336 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7336 : C7336.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7336 : ¬ (C7336.det = 0 ∧ ∀ i, C7336.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7336
def C7337 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7337 : C7337.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7337 : ¬ (C7337.det = 0 ∧ ∀ i, C7337.adjugate i i ≠ 0) := by
  intro h
  have := certificate7337
  rw [h.1] at this
  norm_num at this
def C7338 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7338 : C7338.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7338 : ¬ (C7338.det = 0 ∧ ∀ i, C7338.adjugate i i ≠ 0) := by
  intro h
  have := certificate7338
  rw [h.1] at this
  norm_num at this
def C7339 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7339 : C7339.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7339 : ¬ (C7339.det = 0 ∧ ∀ i, C7339.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7339
def C7340 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7340 : C7340.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7340 : ¬ (C7340.det = 0 ∧ ∀ i, C7340.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7340
def C7341 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7341 : C7341.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7341 : ¬ (C7341.det = 0 ∧ ∀ i, C7341.adjugate i i ≠ 0) := by
  intro h
  have := certificate7341
  rw [h.1] at this
  norm_num at this
def C7342 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7342 : C7342.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7342 : ¬ (C7342.det = 0 ∧ ∀ i, C7342.adjugate i i ≠ 0) := by
  intro h
  have := certificate7342
  rw [h.1] at this
  norm_num at this
def C7343 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7343 : C7343.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7343 : ¬ (C7343.det = 0 ∧ ∀ i, C7343.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7343
def C7344 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7344 : C7344.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7344 : ¬ (C7344.det = 0 ∧ ∀ i, C7344.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7344
def C7345 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7345 : C7345.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7345 : ¬ (C7345.det = 0 ∧ ∀ i, C7345.adjugate i i ≠ 0) := by
  intro h
  have := certificate7345
  rw [h.1] at this
  norm_num at this
def C7346 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7346 : C7346.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7346 : ¬ (C7346.det = 0 ∧ ∀ i, C7346.adjugate i i ≠ 0) := by
  intro h
  have := certificate7346
  rw [h.1] at this
  norm_num at this
def C7347 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7347 : C7347.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7347 : ¬ (C7347.det = 0 ∧ ∀ i, C7347.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7347
def C7348 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7348 : C7348.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7348 : ¬ (C7348.det = 0 ∧ ∀ i, C7348.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7348
def C7349 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7349 : C7349.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7349 : ¬ (C7349.det = 0 ∧ ∀ i, C7349.adjugate i i ≠ 0) := by
  intro h
  have := certificate7349
  rw [h.1] at this
  norm_num at this
def C7350 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7350 : C7350.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7350 : ¬ (C7350.det = 0 ∧ ∀ i, C7350.adjugate i i ≠ 0) := by
  intro h
  have := certificate7350
  rw [h.1] at this
  norm_num at this
def C7351 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7351 : C7351.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7351 : ¬ (C7351.det = 0 ∧ ∀ i, C7351.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7351
def C7352 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7352 : C7352.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7352 : ¬ (C7352.det = 0 ∧ ∀ i, C7352.adjugate i i ≠ 0) := by
  intro h
  have := certificate7352
  rw [h.1] at this
  norm_num at this
def C7353 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7353 : C7353.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7353 : ¬ (C7353.det = 0 ∧ ∀ i, C7353.adjugate i i ≠ 0) := by
  intro h
  have := certificate7353
  rw [h.1] at this
  norm_num at this
def C7354 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7354 : C7354.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7354 : ¬ (C7354.det = 0 ∧ ∀ i, C7354.adjugate i i ≠ 0) := by
  intro h
  have := certificate7354
  rw [h.1] at this
  norm_num at this
def C7355 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7355 : C7355.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7355 : ¬ (C7355.det = 0 ∧ ∀ i, C7355.adjugate i i ≠ 0) := by
  intro h
  have := certificate7355
  rw [h.1] at this
  norm_num at this
def C7356 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7356 : C7356.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7356 : ¬ (C7356.det = 0 ∧ ∀ i, C7356.adjugate i i ≠ 0) := by
  intro h
  have := certificate7356
  rw [h.1] at this
  norm_num at this
def C7357 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7357 : C7357.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7357 : ¬ (C7357.det = 0 ∧ ∀ i, C7357.adjugate i i ≠ 0) := by
  intro h
  have := certificate7357
  rw [h.1] at this
  norm_num at this
def C7358 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7358 : C7358.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7358 : ¬ (C7358.det = 0 ∧ ∀ i, C7358.adjugate i i ≠ 0) := by
  intro h
  have := certificate7358
  rw [h.1] at this
  norm_num at this
def C7359 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7359 : C7359.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7359 : ¬ (C7359.det = 0 ∧ ∀ i, C7359.adjugate i i ≠ 0) := by
  intro h
  have := certificate7359
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0229
