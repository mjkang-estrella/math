import VerifiedDet
namespace Nut8.NewCertificates0137
def C4384 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4384 : C4384.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4384 : ¬ (C4384.det = 0 ∧ ∀ i, C4384.adjugate i i ≠ 0) := by
  intro h
  have := certificate4384
  rw [h.1] at this
  norm_num at this
def C4385 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4385 : C4385.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4385 : ¬ (C4385.det = 0 ∧ ∀ i, C4385.adjugate i i ≠ 0) := by
  intro h
  have := certificate4385
  rw [h.1] at this
  norm_num at this
def C4386 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4386 : C4386.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4386 : ¬ (C4386.det = 0 ∧ ∀ i, C4386.adjugate i i ≠ 0) := by
  intro h
  have := certificate4386
  rw [h.1] at this
  norm_num at this
def C4387 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4387 : C4387.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4387 : ¬ (C4387.det = 0 ∧ ∀ i, C4387.adjugate i i ≠ 0) := by
  intro h
  have := certificate4387
  rw [h.1] at this
  norm_num at this
def C4388 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4388 : C4388.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4388 : ¬ (C4388.det = 0 ∧ ∀ i, C4388.adjugate i i ≠ 0) := by
  intro h
  have := certificate4388
  rw [h.1] at this
  norm_num at this
def C4389 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4389 : C4389.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4389 : ¬ (C4389.det = 0 ∧ ∀ i, C4389.adjugate i i ≠ 0) := by
  intro h
  have := certificate4389
  rw [h.1] at this
  norm_num at this
def C4390 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4390 : C4390.det = (105 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4390 : ¬ (C4390.det = 0 ∧ ∀ i, C4390.adjugate i i ≠ 0) := by
  intro h
  have := certificate4390
  rw [h.1] at this
  norm_num at this
def C4391 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4391 : C4391.det = (-55 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4391 : ¬ (C4391.det = 0 ∧ ∀ i, C4391.adjugate i i ≠ 0) := by
  intro h
  have := certificate4391
  rw [h.1] at this
  norm_num at this
def C4392 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4392 : C4392.det = (57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4392 : ¬ (C4392.det = 0 ∧ ∀ i, C4392.adjugate i i ≠ 0) := by
  intro h
  have := certificate4392
  rw [h.1] at this
  norm_num at this
def C4393 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4393 : C4393.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4393 : ¬ (C4393.det = 0 ∧ ∀ i, C4393.adjugate i i ≠ 0) := by
  intro h
  have := certificate4393
  rw [h.1] at this
  norm_num at this
def C4394 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4394 : C4394.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4394 : ¬ (C4394.det = 0 ∧ ∀ i, C4394.adjugate i i ≠ 0) := by
  intro h
  have := certificate4394
  rw [h.1] at this
  norm_num at this
def C4395 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4395 : C4395.det = (57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4395 : ¬ (C4395.det = 0 ∧ ∀ i, C4395.adjugate i i ≠ 0) := by
  intro h
  have := certificate4395
  rw [h.1] at this
  norm_num at this
def C4396 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4396 : C4396.det = (-55 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4396 : ¬ (C4396.det = 0 ∧ ∀ i, C4396.adjugate i i ≠ 0) := by
  intro h
  have := certificate4396
  rw [h.1] at this
  norm_num at this
def C4397 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4397 : C4397.det = (105 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4397 : ¬ (C4397.det = 0 ∧ ∀ i, C4397.adjugate i i ≠ 0) := by
  intro h
  have := certificate4397
  rw [h.1] at this
  norm_num at this
def C4398 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4398 : C4398.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4398 : ¬ (C4398.det = 0 ∧ ∀ i, C4398.adjugate i i ≠ 0) := by
  intro h
  have := certificate4398
  rw [h.1] at this
  norm_num at this
def C4399 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4399 : C4399.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4399 : ¬ (C4399.det = 0 ∧ ∀ i, C4399.adjugate i i ≠ 0) := by
  intro h
  have := certificate4399
  rw [h.1] at this
  norm_num at this
def C4400 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4400 : C4400.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4400 : ¬ (C4400.det = 0 ∧ ∀ i, C4400.adjugate i i ≠ 0) := by
  intro h
  have := certificate4400
  rw [h.1] at this
  norm_num at this
def C4401 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4401 : C4401.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4401 : ¬ (C4401.det = 0 ∧ ∀ i, C4401.adjugate i i ≠ 0) := by
  intro h
  have := certificate4401
  rw [h.1] at this
  norm_num at this
def C4402 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4402 : C4402.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4402 : ¬ (C4402.det = 0 ∧ ∀ i, C4402.adjugate i i ≠ 0) := by
  intro h
  have := certificate4402
  rw [h.1] at this
  norm_num at this
def C4403 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4403 : C4403.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4403 : ¬ (C4403.det = 0 ∧ ∀ i, C4403.adjugate i i ≠ 0) := by
  intro h
  have := certificate4403
  rw [h.1] at this
  norm_num at this
def C4404 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4404 : C4404.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4404 : ¬ (C4404.det = 0 ∧ ∀ i, C4404.adjugate i i ≠ 0) := by
  intro h
  have := certificate4404
  rw [h.1] at this
  norm_num at this
def C4405 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4405 : C4405.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4405 : ¬ (C4405.det = 0 ∧ ∀ i, C4405.adjugate i i ≠ 0) := by
  intro h
  have := certificate4405
  rw [h.1] at this
  norm_num at this
def C4406 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4406 : C4406.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4406 : ¬ (C4406.det = 0 ∧ ∀ i, C4406.adjugate i i ≠ 0) := by
  intro h
  have := certificate4406
  rw [h.1] at this
  norm_num at this
def C4407 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4407 : C4407.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4407 : ¬ (C4407.det = 0 ∧ ∀ i, C4407.adjugate i i ≠ 0) := by
  intro h
  have := certificate4407
  rw [h.1] at this
  norm_num at this
def C4408 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4408 : C4408.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4408 : ¬ (C4408.det = 0 ∧ ∀ i, C4408.adjugate i i ≠ 0) := by
  intro h
  have := certificate4408
  rw [h.1] at this
  norm_num at this
def C4409 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4409 : C4409.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4409 : ¬ (C4409.det = 0 ∧ ∀ i, C4409.adjugate i i ≠ 0) := by
  intro h
  have := certificate4409
  rw [h.1] at this
  norm_num at this
def C4410 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4410 : C4410.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4410 : ¬ (C4410.det = 0 ∧ ∀ i, C4410.adjugate i i ≠ 0) := by
  intro h
  have := certificate4410
  rw [h.1] at this
  norm_num at this
def C4411 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4411 : C4411.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4411 : ¬ (C4411.det = 0 ∧ ∀ i, C4411.adjugate i i ≠ 0) := by
  intro h
  have := certificate4411
  rw [h.1] at this
  norm_num at this
def C4412 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4412 : C4412.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4412 : ¬ (C4412.det = 0 ∧ ∀ i, C4412.adjugate i i ≠ 0) := by
  intro h
  have := certificate4412
  rw [h.1] at this
  norm_num at this
def C4413 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4413 : C4413.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4413 : ¬ (C4413.det = 0 ∧ ∀ i, C4413.adjugate i i ≠ 0) := by
  intro h
  have := certificate4413
  rw [h.1] at this
  norm_num at this
def C4414 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4414 : C4414.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4414 : ¬ (C4414.det = 0 ∧ ∀ i, C4414.adjugate i i ≠ 0) := by
  intro h
  have := certificate4414
  rw [h.1] at this
  norm_num at this
def C4415 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4415 : C4415.det = (-23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4415 : ¬ (C4415.det = 0 ∧ ∀ i, C4415.adjugate i i ≠ 0) := by
  intro h
  have := certificate4415
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0137
