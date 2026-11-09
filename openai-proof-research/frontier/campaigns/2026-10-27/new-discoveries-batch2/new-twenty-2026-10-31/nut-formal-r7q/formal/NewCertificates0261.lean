import VerifiedDet
namespace Nut8.NewCertificates0261
def C8352 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate8352 : C8352.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8352 : ¬ (C8352.det = 0 ∧ ∀ i, C8352.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate8352
def C8353 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate8353 : C8353.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8353 : ¬ (C8353.det = 0 ∧ ∀ i, C8353.adjugate i i ≠ 0) := by
  intro h
  have := certificate8353
  rw [h.1] at this
  norm_num at this
def C8354 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate8354 : C8354.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8354 : ¬ (C8354.det = 0 ∧ ∀ i, C8354.adjugate i i ≠ 0) := by
  intro h
  have := certificate8354
  rw [h.1] at this
  norm_num at this
def C8355 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate8355 : C8355.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8355 : ¬ (C8355.det = 0 ∧ ∀ i, C8355.adjugate i i ≠ 0) := by
  intro h
  have := certificate8355
  rw [h.1] at this
  norm_num at this
def C8356 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8356 : C8356.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8356 : ¬ (C8356.det = 0 ∧ ∀ i, C8356.adjugate i i ≠ 0) := by
  intro h
  have := certificate8356
  rw [h.1] at this
  norm_num at this
def C8357 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8357 : C8357.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8357 : ¬ (C8357.det = 0 ∧ ∀ i, C8357.adjugate i i ≠ 0) := by
  intro h
  have := certificate8357
  rw [h.1] at this
  norm_num at this
def C8358 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8358 : C8358.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8358 : ¬ (C8358.det = 0 ∧ ∀ i, C8358.adjugate i i ≠ 0) := by
  intro h
  have := certificate8358
  rw [h.1] at this
  norm_num at this
def C8359 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8359 : C8359.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8359 : ¬ (C8359.det = 0 ∧ ∀ i, C8359.adjugate i i ≠ 0) := by
  intro h
  have := certificate8359
  rw [h.1] at this
  norm_num at this
def C8360 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8360 : C8360.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8360 : ¬ (C8360.det = 0 ∧ ∀ i, C8360.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8360
def C8361 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8361 : C8361.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8361 : ¬ (C8361.det = 0 ∧ ∀ i, C8361.adjugate i i ≠ 0) := by
  intro h
  have := certificate8361
  rw [h.1] at this
  norm_num at this
def C8362 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8362 : C8362.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8362 : ¬ (C8362.det = 0 ∧ ∀ i, C8362.adjugate i i ≠ 0) := by
  intro h
  have := certificate8362
  rw [h.1] at this
  norm_num at this
def C8363 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8363 : C8363.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8363 : ¬ (C8363.det = 0 ∧ ∀ i, C8363.adjugate i i ≠ 0) := by
  intro h
  have := certificate8363
  rw [h.1] at this
  norm_num at this
def C8364 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8364 : C8364.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8364 : ¬ (C8364.det = 0 ∧ ∀ i, C8364.adjugate i i ≠ 0) := by
  intro h
  have := certificate8364
  rw [h.1] at this
  norm_num at this
def C8365 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8365 : C8365.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8365 : ¬ (C8365.det = 0 ∧ ∀ i, C8365.adjugate i i ≠ 0) := by
  intro h
  have := certificate8365
  rw [h.1] at this
  norm_num at this
def C8366 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8366 : C8366.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8366 : ¬ (C8366.det = 0 ∧ ∀ i, C8366.adjugate i i ≠ 0) := by
  intro h
  have := certificate8366
  rw [h.1] at this
  norm_num at this
def C8367 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8367 : C8367.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8367 : ¬ (C8367.det = 0 ∧ ∀ i, C8367.adjugate i i ≠ 0) := by
  intro h
  have := certificate8367
  rw [h.1] at this
  norm_num at this
def C8368 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8368 : C8368.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8368 : ¬ (C8368.det = 0 ∧ ∀ i, C8368.adjugate i i ≠ 0) := by
  intro h
  have := certificate8368
  rw [h.1] at this
  norm_num at this
def C8369 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8369 : C8369.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8369 : ¬ (C8369.det = 0 ∧ ∀ i, C8369.adjugate i i ≠ 0) := by
  intro h
  have := certificate8369
  rw [h.1] at this
  norm_num at this
def C8370 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8370 : C8370.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8370 : ¬ (C8370.det = 0 ∧ ∀ i, C8370.adjugate i i ≠ 0) := by
  intro h
  have := certificate8370
  rw [h.1] at this
  norm_num at this
def C8371 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8371 : C8371.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8371 : ¬ (C8371.det = 0 ∧ ∀ i, C8371.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8371
def C8372 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate8372 : C8372.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8372 : ¬ (C8372.det = 0 ∧ ∀ i, C8372.adjugate i i ≠ 0) := by
  intro h
  have := certificate8372
  rw [h.1] at this
  norm_num at this
def C8373 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate8373 : C8373.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8373 : ¬ (C8373.det = 0 ∧ ∀ i, C8373.adjugate i i ≠ 0) := by
  intro h
  have := certificate8373
  rw [h.1] at this
  norm_num at this
def C8374 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate8374 : C8374.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8374 : ¬ (C8374.det = 0 ∧ ∀ i, C8374.adjugate i i ≠ 0) := by
  intro h
  have := certificate8374
  rw [h.1] at this
  norm_num at this
def C8375 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate8375 : C8375.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8375 : ¬ (C8375.det = 0 ∧ ∀ i, C8375.adjugate i i ≠ 0) := by
  intro h
  have := certificate8375
  rw [h.1] at this
  norm_num at this
def C8376 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate8376 : C8376.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8376 : ¬ (C8376.det = 0 ∧ ∀ i, C8376.adjugate i i ≠ 0) := by
  intro h
  have := certificate8376
  rw [h.1] at this
  norm_num at this
def C8377 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate8377 : C8377.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8377 : ¬ (C8377.det = 0 ∧ ∀ i, C8377.adjugate i i ≠ 0) := by
  intro h
  have := certificate8377
  rw [h.1] at this
  norm_num at this
def C8378 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate8378 : C8378.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8378 : ¬ (C8378.det = 0 ∧ ∀ i, C8378.adjugate i i ≠ 0) := by
  intro h
  have := certificate8378
  rw [h.1] at this
  norm_num at this
def C8379 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate8379 : C8379.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8379 : ¬ (C8379.det = 0 ∧ ∀ i, C8379.adjugate i i ≠ 0) := by
  intro h
  have := certificate8379
  rw [h.1] at this
  norm_num at this
def C8380 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8380 : C8380.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8380 : ¬ (C8380.det = 0 ∧ ∀ i, C8380.adjugate i i ≠ 0) := by
  intro h
  have := certificate8380
  rw [h.1] at this
  norm_num at this
def C8381 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8381 : C8381.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8381 : ¬ (C8381.det = 0 ∧ ∀ i, C8381.adjugate i i ≠ 0) := by
  intro h
  have := certificate8381
  rw [h.1] at this
  norm_num at this
def C8382 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate8382 : C8382.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8382 : ¬ (C8382.det = 0 ∧ ∀ i, C8382.adjugate i i ≠ 0) := by
  intro h
  have := certificate8382
  rw [h.1] at this
  norm_num at this
def C8383 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate8383 : C8383.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8383 : ¬ (C8383.det = 0 ∧ ∀ i, C8383.adjugate i i ≠ 0) := by
  intro h
  have := certificate8383
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0261
