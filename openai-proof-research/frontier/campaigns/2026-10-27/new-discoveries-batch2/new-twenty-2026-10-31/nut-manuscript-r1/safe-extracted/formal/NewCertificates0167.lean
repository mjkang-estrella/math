import VerifiedDet
namespace Nut8.NewCertificates0167
def C5344 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5344 : C5344.det = (-57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5344 : ¬ (C5344.det = 0 ∧ ∀ i, C5344.adjugate i i ≠ 0) := by
  intro h
  have := certificate5344
  rw [h.1] at this
  norm_num at this
def C5345 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5345 : C5345.det = (107 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5345 : ¬ (C5345.det = 0 ∧ ∀ i, C5345.adjugate i i ≠ 0) := by
  intro h
  have := certificate5345
  rw [h.1] at this
  norm_num at this
def C5346 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5346 : C5346.det = (107 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5346 : ¬ (C5346.det = 0 ∧ ∀ i, C5346.adjugate i i ≠ 0) := by
  intro h
  have := certificate5346
  rw [h.1] at this
  norm_num at this
def C5347 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5347 : C5347.det = (-57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5347 : ¬ (C5347.det = 0 ∧ ∀ i, C5347.adjugate i i ≠ 0) := by
  intro h
  have := certificate5347
  rw [h.1] at this
  norm_num at this
def C5348 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5348 : C5348.det = (-41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5348 : ¬ (C5348.det = 0 ∧ ∀ i, C5348.adjugate i i ≠ 0) := by
  intro h
  have := certificate5348
  rw [h.1] at this
  norm_num at this
def C5349 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5349 : C5349.det = (59 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5349 : ¬ (C5349.det = 0 ∧ ∀ i, C5349.adjugate i i ≠ 0) := by
  intro h
  have := certificate5349
  rw [h.1] at this
  norm_num at this
def C5350 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5350 : C5350.det = (59 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5350 : ¬ (C5350.det = 0 ∧ ∀ i, C5350.adjugate i i ≠ 0) := by
  intro h
  have := certificate5350
  rw [h.1] at this
  norm_num at this
def C5351 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5351 : C5351.det = (-41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5351 : ¬ (C5351.det = 0 ∧ ∀ i, C5351.adjugate i i ≠ 0) := by
  intro h
  have := certificate5351
  rw [h.1] at this
  norm_num at this
def C5352 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5352 : C5352.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5352 : ¬ (C5352.det = 0 ∧ ∀ i, C5352.adjugate i i ≠ 0) := by
  intro h
  have := certificate5352
  rw [h.1] at this
  norm_num at this
def C5353 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5353 : C5353.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5353 : ¬ (C5353.det = 0 ∧ ∀ i, C5353.adjugate i i ≠ 0) := by
  intro h
  have := certificate5353
  rw [h.1] at this
  norm_num at this
def C5354 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5354 : C5354.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5354 : ¬ (C5354.det = 0 ∧ ∀ i, C5354.adjugate i i ≠ 0) := by
  intro h
  have := certificate5354
  rw [h.1] at this
  norm_num at this
def C5355 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5355 : C5355.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5355 : ¬ (C5355.det = 0 ∧ ∀ i, C5355.adjugate i i ≠ 0) := by
  intro h
  have := certificate5355
  rw [h.1] at this
  norm_num at this
def C5356 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5356 : C5356.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5356 : ¬ (C5356.det = 0 ∧ ∀ i, C5356.adjugate i i ≠ 0) := by
  intro h
  have := certificate5356
  rw [h.1] at this
  norm_num at this
def C5357 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5357 : C5357.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5357 : ¬ (C5357.det = 0 ∧ ∀ i, C5357.adjugate i i ≠ 0) := by
  intro h
  have := certificate5357
  rw [h.1] at this
  norm_num at this
def C5358 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5358 : C5358.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5358 : ¬ (C5358.det = 0 ∧ ∀ i, C5358.adjugate i i ≠ 0) := by
  intro h
  have := certificate5358
  rw [h.1] at this
  norm_num at this
def C5359 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5359 : C5359.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5359 : ¬ (C5359.det = 0 ∧ ∀ i, C5359.adjugate i i ≠ 0) := by
  intro h
  have := certificate5359
  rw [h.1] at this
  norm_num at this
def C5360 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5360 : C5360.det = (-57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5360 : ¬ (C5360.det = 0 ∧ ∀ i, C5360.adjugate i i ≠ 0) := by
  intro h
  have := certificate5360
  rw [h.1] at this
  norm_num at this
def C5361 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5361 : C5361.det = (107 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5361 : ¬ (C5361.det = 0 ∧ ∀ i, C5361.adjugate i i ≠ 0) := by
  intro h
  have := certificate5361
  rw [h.1] at this
  norm_num at this
def C5362 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5362 : C5362.det = (107 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5362 : ¬ (C5362.det = 0 ∧ ∀ i, C5362.adjugate i i ≠ 0) := by
  intro h
  have := certificate5362
  rw [h.1] at this
  norm_num at this
def C5363 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5363 : C5363.det = (-57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5363 : ¬ (C5363.det = 0 ∧ ∀ i, C5363.adjugate i i ≠ 0) := by
  intro h
  have := certificate5363
  rw [h.1] at this
  norm_num at this
def C5364 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5364 : C5364.det = (-41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5364 : ¬ (C5364.det = 0 ∧ ∀ i, C5364.adjugate i i ≠ 0) := by
  intro h
  have := certificate5364
  rw [h.1] at this
  norm_num at this
def C5365 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5365 : C5365.det = (59 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5365 : ¬ (C5365.det = 0 ∧ ∀ i, C5365.adjugate i i ≠ 0) := by
  intro h
  have := certificate5365
  rw [h.1] at this
  norm_num at this
def C5366 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5366 : C5366.det = (59 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5366 : ¬ (C5366.det = 0 ∧ ∀ i, C5366.adjugate i i ≠ 0) := by
  intro h
  have := certificate5366
  rw [h.1] at this
  norm_num at this
def C5367 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5367 : C5367.det = (-41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5367 : ¬ (C5367.det = 0 ∧ ∀ i, C5367.adjugate i i ≠ 0) := by
  intro h
  have := certificate5367
  rw [h.1] at this
  norm_num at this
def C5368 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5368 : C5368.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5368 : ¬ (C5368.det = 0 ∧ ∀ i, C5368.adjugate i i ≠ 0) := by
  intro h
  have := certificate5368
  rw [h.1] at this
  norm_num at this
def C5369 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5369 : C5369.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5369 : ¬ (C5369.det = 0 ∧ ∀ i, C5369.adjugate i i ≠ 0) := by
  intro h
  have := certificate5369
  rw [h.1] at this
  norm_num at this
def C5370 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5370 : C5370.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5370 : ¬ (C5370.det = 0 ∧ ∀ i, C5370.adjugate i i ≠ 0) := by
  intro h
  have := certificate5370
  rw [h.1] at this
  norm_num at this
def C5371 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5371 : C5371.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5371 : ¬ (C5371.det = 0 ∧ ∀ i, C5371.adjugate i i ≠ 0) := by
  intro h
  have := certificate5371
  rw [h.1] at this
  norm_num at this
def C5372 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5372 : C5372.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5372 : ¬ (C5372.det = 0 ∧ ∀ i, C5372.adjugate i i ≠ 0) := by
  intro h
  have := certificate5372
  rw [h.1] at this
  norm_num at this
def C5373 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5373 : C5373.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5373 : ¬ (C5373.det = 0 ∧ ∀ i, C5373.adjugate i i ≠ 0) := by
  intro h
  have := certificate5373
  rw [h.1] at this
  norm_num at this
def C5374 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5374 : C5374.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5374 : ¬ (C5374.det = 0 ∧ ∀ i, C5374.adjugate i i ≠ 0) := by
  intro h
  have := certificate5374
  rw [h.1] at this
  norm_num at this
def C5375 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5375 : C5375.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5375 : ¬ (C5375.det = 0 ∧ ∀ i, C5375.adjugate i i ≠ 0) := by
  intro h
  have := certificate5375
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0167
