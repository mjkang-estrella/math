import VerifiedDet
namespace Nut8.NewCertificates0230
def C7360 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7360 : C7360.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7360 : ¬ (C7360.det = 0 ∧ ∀ i, C7360.adjugate i i ≠ 0) := by
  intro h
  have := certificate7360
  rw [h.1] at this
  norm_num at this
def C7361 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7361 : C7361.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7361 : ¬ (C7361.det = 0 ∧ ∀ i, C7361.adjugate i i ≠ 0) := by
  intro h
  have := certificate7361
  rw [h.1] at this
  norm_num at this
def C7362 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7362 : C7362.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7362 : ¬ (C7362.det = 0 ∧ ∀ i, C7362.adjugate i i ≠ 0) := by
  intro h
  have := certificate7362
  rw [h.1] at this
  norm_num at this
def C7363 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7363 : C7363.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7363 : ¬ (C7363.det = 0 ∧ ∀ i, C7363.adjugate i i ≠ 0) := by
  intro h
  have := certificate7363
  rw [h.1] at this
  norm_num at this
def C7364 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7364 : C7364.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7364 : ¬ (C7364.det = 0 ∧ ∀ i, C7364.adjugate i i ≠ 0) := by
  intro h
  have := certificate7364
  rw [h.1] at this
  norm_num at this
def C7365 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7365 : C7365.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7365 : ¬ (C7365.det = 0 ∧ ∀ i, C7365.adjugate i i ≠ 0) := by
  intro h
  have := certificate7365
  rw [h.1] at this
  norm_num at this
def C7366 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7366 : C7366.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7366 : ¬ (C7366.det = 0 ∧ ∀ i, C7366.adjugate i i ≠ 0) := by
  intro h
  have := certificate7366
  rw [h.1] at this
  norm_num at this
def C7367 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7367 : C7367.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7367 : ¬ (C7367.det = 0 ∧ ∀ i, C7367.adjugate i i ≠ 0) := by
  intro h
  have := certificate7367
  rw [h.1] at this
  norm_num at this
def C7368 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7368 : C7368.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7368 : ¬ (C7368.det = 0 ∧ ∀ i, C7368.adjugate i i ≠ 0) := by
  intro h
  have := certificate7368
  rw [h.1] at this
  norm_num at this
def C7369 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7369 : C7369.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7369 : ¬ (C7369.det = 0 ∧ ∀ i, C7369.adjugate i i ≠ 0) := by
  intro h
  have := certificate7369
  rw [h.1] at this
  norm_num at this
def C7370 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7370 : C7370.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7370 : ¬ (C7370.det = 0 ∧ ∀ i, C7370.adjugate i i ≠ 0) := by
  intro h
  have := certificate7370
  rw [h.1] at this
  norm_num at this
def C7371 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7371 : C7371.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7371 : ¬ (C7371.det = 0 ∧ ∀ i, C7371.adjugate i i ≠ 0) := by
  intro h
  have := certificate7371
  rw [h.1] at this
  norm_num at this
def C7372 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7372 : C7372.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7372 : ¬ (C7372.det = 0 ∧ ∀ i, C7372.adjugate i i ≠ 0) := by
  intro h
  have := certificate7372
  rw [h.1] at this
  norm_num at this
def C7373 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7373 : C7373.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7373 : ¬ (C7373.det = 0 ∧ ∀ i, C7373.adjugate i i ≠ 0) := by
  intro h
  have := certificate7373
  rw [h.1] at this
  norm_num at this
def C7374 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7374 : C7374.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7374 : ¬ (C7374.det = 0 ∧ ∀ i, C7374.adjugate i i ≠ 0) := by
  intro h
  have := certificate7374
  rw [h.1] at this
  norm_num at this
def C7375 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7375 : C7375.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7375 : ¬ (C7375.det = 0 ∧ ∀ i, C7375.adjugate i i ≠ 0) := by
  intro h
  have := certificate7375
  rw [h.1] at this
  norm_num at this
def C7376 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7376 : C7376.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7376 : ¬ (C7376.det = 0 ∧ ∀ i, C7376.adjugate i i ≠ 0) := by
  intro h
  have := certificate7376
  rw [h.1] at this
  norm_num at this
def C7377 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7377 : C7377.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7377 : ¬ (C7377.det = 0 ∧ ∀ i, C7377.adjugate i i ≠ 0) := by
  intro h
  have := certificate7377
  rw [h.1] at this
  norm_num at this
def C7378 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7378 : C7378.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7378 : ¬ (C7378.det = 0 ∧ ∀ i, C7378.adjugate i i ≠ 0) := by
  intro h
  have := certificate7378
  rw [h.1] at this
  norm_num at this
def C7379 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7379 : C7379.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7379 : ¬ (C7379.det = 0 ∧ ∀ i, C7379.adjugate i i ≠ 0) := by
  intro h
  have := certificate7379
  rw [h.1] at this
  norm_num at this
def C7380 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7380 : C7380.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7380 : ¬ (C7380.det = 0 ∧ ∀ i, C7380.adjugate i i ≠ 0) := by
  intro h
  have := certificate7380
  rw [h.1] at this
  norm_num at this
def C7381 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7381 : C7381.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7381 : ¬ (C7381.det = 0 ∧ ∀ i, C7381.adjugate i i ≠ 0) := by
  intro h
  have := certificate7381
  rw [h.1] at this
  norm_num at this
def C7382 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7382 : C7382.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7382 : ¬ (C7382.det = 0 ∧ ∀ i, C7382.adjugate i i ≠ 0) := by
  intro h
  have := certificate7382
  rw [h.1] at this
  norm_num at this
def C7383 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7383 : C7383.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7383 : ¬ (C7383.det = 0 ∧ ∀ i, C7383.adjugate i i ≠ 0) := by
  intro h
  have := certificate7383
  rw [h.1] at this
  norm_num at this
def C7384 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7384 : C7384.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7384 : ¬ (C7384.det = 0 ∧ ∀ i, C7384.adjugate i i ≠ 0) := by
  intro h
  have := certificate7384
  rw [h.1] at this
  norm_num at this
def C7385 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7385 : C7385.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7385 : ¬ (C7385.det = 0 ∧ ∀ i, C7385.adjugate i i ≠ 0) := by
  intro h
  have := certificate7385
  rw [h.1] at this
  norm_num at this
def C7386 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7386 : C7386.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7386 : ¬ (C7386.det = 0 ∧ ∀ i, C7386.adjugate i i ≠ 0) := by
  intro h
  have := certificate7386
  rw [h.1] at this
  norm_num at this
def C7387 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7387 : C7387.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7387 : ¬ (C7387.det = 0 ∧ ∀ i, C7387.adjugate i i ≠ 0) := by
  intro h
  have := certificate7387
  rw [h.1] at this
  norm_num at this
def C7388 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7388 : C7388.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7388 : ¬ (C7388.det = 0 ∧ ∀ i, C7388.adjugate i i ≠ 0) := by
  intro h
  have := certificate7388
  rw [h.1] at this
  norm_num at this
def C7389 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7389 : C7389.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7389 : ¬ (C7389.det = 0 ∧ ∀ i, C7389.adjugate i i ≠ 0) := by
  intro h
  have := certificate7389
  rw [h.1] at this
  norm_num at this
def C7390 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7390 : C7390.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7390 : ¬ (C7390.det = 0 ∧ ∀ i, C7390.adjugate i i ≠ 0) := by
  intro h
  have := certificate7390
  rw [h.1] at this
  norm_num at this
def C7391 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7391 : C7391.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7391 : ¬ (C7391.det = 0 ∧ ∀ i, C7391.adjugate i i ≠ 0) := by
  intro h
  have := certificate7391
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0230
