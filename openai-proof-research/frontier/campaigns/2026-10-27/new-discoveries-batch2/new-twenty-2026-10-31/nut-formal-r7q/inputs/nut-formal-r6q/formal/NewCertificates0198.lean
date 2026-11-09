import VerifiedDet
namespace Nut8.NewCertificates0198
def C6336 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6336 : C6336.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6336 : ¬ (C6336.det = 0 ∧ ∀ i, C6336.adjugate i i ≠ 0) := by
  intro h
  have := certificate6336
  rw [h.1] at this
  norm_num at this
def C6337 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6337 : C6337.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6337 : ¬ (C6337.det = 0 ∧ ∀ i, C6337.adjugate i i ≠ 0) := by
  intro h
  have := certificate6337
  rw [h.1] at this
  norm_num at this
def C6338 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6338 : C6338.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6338 : ¬ (C6338.det = 0 ∧ ∀ i, C6338.adjugate i i ≠ 0) := by
  intro h
  have := certificate6338
  rw [h.1] at this
  norm_num at this
def C6339 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6339 : C6339.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6339 : ¬ (C6339.det = 0 ∧ ∀ i, C6339.adjugate i i ≠ 0) := by
  intro h
  have := certificate6339
  rw [h.1] at this
  norm_num at this
def C6340 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6340 : C6340.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6340 : ¬ (C6340.det = 0 ∧ ∀ i, C6340.adjugate i i ≠ 0) := by
  intro h
  have := certificate6340
  rw [h.1] at this
  norm_num at this
def C6341 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6341 : C6341.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6341 : ¬ (C6341.det = 0 ∧ ∀ i, C6341.adjugate i i ≠ 0) := by
  intro h
  have := certificate6341
  rw [h.1] at this
  norm_num at this
def C6342 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6342 : C6342.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6342 : ¬ (C6342.det = 0 ∧ ∀ i, C6342.adjugate i i ≠ 0) := by
  intro h
  have := certificate6342
  rw [h.1] at this
  norm_num at this
def C6343 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6343 : C6343.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6343 : ¬ (C6343.det = 0 ∧ ∀ i, C6343.adjugate i i ≠ 0) := by
  intro h
  have := certificate6343
  rw [h.1] at this
  norm_num at this
def C6344 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6344 : C6344.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6344 : ¬ (C6344.det = 0 ∧ ∀ i, C6344.adjugate i i ≠ 0) := by
  intro h
  have := certificate6344
  rw [h.1] at this
  norm_num at this
def C6345 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6345 : C6345.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6345 : ¬ (C6345.det = 0 ∧ ∀ i, C6345.adjugate i i ≠ 0) := by
  intro h
  have := certificate6345
  rw [h.1] at this
  norm_num at this
def C6346 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6346 : C6346.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6346 : ¬ (C6346.det = 0 ∧ ∀ i, C6346.adjugate i i ≠ 0) := by
  intro h
  have := certificate6346
  rw [h.1] at this
  norm_num at this
def C6347 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6347 : C6347.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6347 : ¬ (C6347.det = 0 ∧ ∀ i, C6347.adjugate i i ≠ 0) := by
  intro h
  have := certificate6347
  rw [h.1] at this
  norm_num at this
def C6348 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6348 : C6348.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6348 : ¬ (C6348.det = 0 ∧ ∀ i, C6348.adjugate i i ≠ 0) := by
  intro h
  have := certificate6348
  rw [h.1] at this
  norm_num at this
def C6349 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6349 : C6349.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6349 : ¬ (C6349.det = 0 ∧ ∀ i, C6349.adjugate i i ≠ 0) := by
  intro h
  have := certificate6349
  rw [h.1] at this
  norm_num at this
def C6350 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6350 : C6350.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6350 : ¬ (C6350.det = 0 ∧ ∀ i, C6350.adjugate i i ≠ 0) := by
  intro h
  have := certificate6350
  rw [h.1] at this
  norm_num at this
def C6351 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6351 : C6351.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6351 : ¬ (C6351.det = 0 ∧ ∀ i, C6351.adjugate i i ≠ 0) := by
  intro h
  have := certificate6351
  rw [h.1] at this
  norm_num at this
def C6352 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6352 : C6352.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6352 : ¬ (C6352.det = 0 ∧ ∀ i, C6352.adjugate i i ≠ 0) := by
  intro h
  have := certificate6352
  rw [h.1] at this
  norm_num at this
def C6353 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6353 : C6353.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6353 : ¬ (C6353.det = 0 ∧ ∀ i, C6353.adjugate i i ≠ 0) := by
  intro h
  have := certificate6353
  rw [h.1] at this
  norm_num at this
def C6354 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6354 : C6354.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6354 : ¬ (C6354.det = 0 ∧ ∀ i, C6354.adjugate i i ≠ 0) := by
  intro h
  have := certificate6354
  rw [h.1] at this
  norm_num at this
def C6355 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6355 : C6355.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6355 : ¬ (C6355.det = 0 ∧ ∀ i, C6355.adjugate i i ≠ 0) := by
  intro h
  have := certificate6355
  rw [h.1] at this
  norm_num at this
def C6356 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6356 : C6356.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6356 : ¬ (C6356.det = 0 ∧ ∀ i, C6356.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6356
def C6357 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6357 : C6357.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6357 : ¬ (C6357.det = 0 ∧ ∀ i, C6357.adjugate i i ≠ 0) := by
  intro h
  have := certificate6357
  rw [h.1] at this
  norm_num at this
def C6358 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6358 : C6358.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6358 : ¬ (C6358.det = 0 ∧ ∀ i, C6358.adjugate i i ≠ 0) := by
  intro h
  have := certificate6358
  rw [h.1] at this
  norm_num at this
def C6359 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6359 : C6359.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6359 : ¬ (C6359.det = 0 ∧ ∀ i, C6359.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6359
def C6360 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6360 : C6360.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6360 : ¬ (C6360.det = 0 ∧ ∀ i, C6360.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6360
def C6361 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6361 : C6361.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6361 : ¬ (C6361.det = 0 ∧ ∀ i, C6361.adjugate i i ≠ 0) := by
  intro h
  have := certificate6361
  rw [h.1] at this
  norm_num at this
def C6362 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6362 : C6362.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6362 : ¬ (C6362.det = 0 ∧ ∀ i, C6362.adjugate i i ≠ 0) := by
  intro h
  have := certificate6362
  rw [h.1] at this
  norm_num at this
def C6363 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6363 : C6363.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6363 : ¬ (C6363.det = 0 ∧ ∀ i, C6363.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6363
def C6364 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6364 : C6364.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6364 : ¬ (C6364.det = 0 ∧ ∀ i, C6364.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6364
def C6365 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6365 : C6365.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6365 : ¬ (C6365.det = 0 ∧ ∀ i, C6365.adjugate i i ≠ 0) := by
  intro h
  have := certificate6365
  rw [h.1] at this
  norm_num at this
def C6366 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6366 : C6366.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6366 : ¬ (C6366.det = 0 ∧ ∀ i, C6366.adjugate i i ≠ 0) := by
  intro h
  have := certificate6366
  rw [h.1] at this
  norm_num at this
def C6367 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6367 : C6367.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6367 : ¬ (C6367.det = 0 ∧ ∀ i, C6367.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6367
end Nut8.NewCertificates0198
