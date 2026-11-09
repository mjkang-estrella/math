import VerifiedDet
namespace Nut8.NewCertificates0168
def C5376 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5376 : C5376.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5376 : ¬ (C5376.det = 0 ∧ ∀ i, C5376.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5376
def C5377 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5377 : C5377.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5377 : ¬ (C5377.det = 0 ∧ ∀ i, C5377.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5377
def C5378 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5378 : C5378.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5378 : ¬ (C5378.det = 0 ∧ ∀ i, C5378.adjugate i i ≠ 0) := by
  intro h
  have := certificate5378
  rw [h.1] at this
  norm_num at this
def C5379 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5379 : C5379.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5379 : ¬ (C5379.det = 0 ∧ ∀ i, C5379.adjugate i i ≠ 0) := by
  intro h
  have := certificate5379
  rw [h.1] at this
  norm_num at this
def C5380 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5380 : C5380.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5380 : ¬ (C5380.det = 0 ∧ ∀ i, C5380.adjugate i i ≠ 0) := by
  intro h
  have := certificate5380
  rw [h.1] at this
  norm_num at this
def C5381 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5381 : C5381.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5381 : ¬ (C5381.det = 0 ∧ ∀ i, C5381.adjugate i i ≠ 0) := by
  intro h
  have := certificate5381
  rw [h.1] at this
  norm_num at this
def C5382 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5382 : C5382.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5382 : ¬ (C5382.det = 0 ∧ ∀ i, C5382.adjugate i i ≠ 0) := by
  intro h
  have := certificate5382
  rw [h.1] at this
  norm_num at this
def C5383 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5383 : C5383.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5383 : ¬ (C5383.det = 0 ∧ ∀ i, C5383.adjugate i i ≠ 0) := by
  intro h
  have := certificate5383
  rw [h.1] at this
  norm_num at this
def C5384 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5384 : C5384.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5384 : ¬ (C5384.det = 0 ∧ ∀ i, C5384.adjugate i i ≠ 0) := by
  intro h
  have := certificate5384
  rw [h.1] at this
  norm_num at this
def C5385 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5385 : C5385.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5385 : ¬ (C5385.det = 0 ∧ ∀ i, C5385.adjugate i i ≠ 0) := by
  intro h
  have := certificate5385
  rw [h.1] at this
  norm_num at this
def C5386 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5386 : C5386.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5386 : ¬ (C5386.det = 0 ∧ ∀ i, C5386.adjugate i i ≠ 0) := by
  intro h
  have := certificate5386
  rw [h.1] at this
  norm_num at this
def C5387 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5387 : C5387.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5387 : ¬ (C5387.det = 0 ∧ ∀ i, C5387.adjugate i i ≠ 0) := by
  intro h
  have := certificate5387
  rw [h.1] at this
  norm_num at this
def C5388 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5388 : C5388.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5388 : ¬ (C5388.det = 0 ∧ ∀ i, C5388.adjugate i i ≠ 0) := by
  intro h
  have := certificate5388
  rw [h.1] at this
  norm_num at this
def C5389 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5389 : C5389.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5389 : ¬ (C5389.det = 0 ∧ ∀ i, C5389.adjugate i i ≠ 0) := by
  intro h
  have := certificate5389
  rw [h.1] at this
  norm_num at this
def C5390 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5390 : C5390.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5390 : ¬ (C5390.det = 0 ∧ ∀ i, C5390.adjugate i i ≠ 0) := by
  intro h
  have := certificate5390
  rw [h.1] at this
  norm_num at this
def C5391 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5391 : C5391.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5391 : ¬ (C5391.det = 0 ∧ ∀ i, C5391.adjugate i i ≠ 0) := by
  intro h
  have := certificate5391
  rw [h.1] at this
  norm_num at this
def C5392 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5392 : C5392.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5392 : ¬ (C5392.det = 0 ∧ ∀ i, C5392.adjugate i i ≠ 0) := by
  intro h
  have := certificate5392
  rw [h.1] at this
  norm_num at this
def C5393 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5393 : C5393.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5393 : ¬ (C5393.det = 0 ∧ ∀ i, C5393.adjugate i i ≠ 0) := by
  intro h
  have := certificate5393
  rw [h.1] at this
  norm_num at this
def C5394 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5394 : C5394.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5394 : ¬ (C5394.det = 0 ∧ ∀ i, C5394.adjugate i i ≠ 0) := by
  intro h
  have := certificate5394
  rw [h.1] at this
  norm_num at this
def C5395 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5395 : C5395.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5395 : ¬ (C5395.det = 0 ∧ ∀ i, C5395.adjugate i i ≠ 0) := by
  intro h
  have := certificate5395
  rw [h.1] at this
  norm_num at this
def C5396 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5396 : C5396.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5396 : ¬ (C5396.det = 0 ∧ ∀ i, C5396.adjugate i i ≠ 0) := by
  intro h
  have := certificate5396
  rw [h.1] at this
  norm_num at this
def C5397 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5397 : C5397.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5397 : ¬ (C5397.det = 0 ∧ ∀ i, C5397.adjugate i i ≠ 0) := by
  intro h
  have := certificate5397
  rw [h.1] at this
  norm_num at this
def C5398 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5398 : C5398.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5398 : ¬ (C5398.det = 0 ∧ ∀ i, C5398.adjugate i i ≠ 0) := by
  intro h
  have := certificate5398
  rw [h.1] at this
  norm_num at this
def C5399 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5399 : C5399.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5399 : ¬ (C5399.det = 0 ∧ ∀ i, C5399.adjugate i i ≠ 0) := by
  intro h
  have := certificate5399
  rw [h.1] at this
  norm_num at this
def C5400 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5400 : C5400.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5400 : ¬ (C5400.det = 0 ∧ ∀ i, C5400.adjugate i i ≠ 0) := by
  intro h
  have := certificate5400
  rw [h.1] at this
  norm_num at this
def C5401 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5401 : C5401.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5401 : ¬ (C5401.det = 0 ∧ ∀ i, C5401.adjugate i i ≠ 0) := by
  intro h
  have := certificate5401
  rw [h.1] at this
  norm_num at this
def C5402 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5402 : C5402.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5402 : ¬ (C5402.det = 0 ∧ ∀ i, C5402.adjugate i i ≠ 0) := by
  intro h
  have := certificate5402
  rw [h.1] at this
  norm_num at this
def C5403 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5403 : C5403.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5403 : ¬ (C5403.det = 0 ∧ ∀ i, C5403.adjugate i i ≠ 0) := by
  intro h
  have := certificate5403
  rw [h.1] at this
  norm_num at this
def C5404 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5404 : C5404.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5404 : ¬ (C5404.det = 0 ∧ ∀ i, C5404.adjugate i i ≠ 0) := by
  intro h
  have := certificate5404
  rw [h.1] at this
  norm_num at this
def C5405 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5405 : C5405.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5405 : ¬ (C5405.det = 0 ∧ ∀ i, C5405.adjugate i i ≠ 0) := by
  intro h
  have := certificate5405
  rw [h.1] at this
  norm_num at this
def C5406 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5406 : C5406.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5406 : ¬ (C5406.det = 0 ∧ ∀ i, C5406.adjugate i i ≠ 0) := by
  intro h
  have := certificate5406
  rw [h.1] at this
  norm_num at this
def C5407 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5407 : C5407.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5407 : ¬ (C5407.det = 0 ∧ ∀ i, C5407.adjugate i i ≠ 0) := by
  intro h
  have := certificate5407
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0168
