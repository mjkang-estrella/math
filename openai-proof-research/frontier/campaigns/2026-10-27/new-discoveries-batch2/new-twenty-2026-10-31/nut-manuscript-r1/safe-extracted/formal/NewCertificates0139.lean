import VerifiedDet
namespace Nut8.NewCertificates0139
def C4448 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4448 : C4448.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4448 : ¬ (C4448.det = 0 ∧ ∀ i, C4448.adjugate i i ≠ 0) := by
  intro h
  have := certificate4448
  rw [h.1] at this
  norm_num at this
def C4449 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4449 : C4449.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4449 : ¬ (C4449.det = 0 ∧ ∀ i, C4449.adjugate i i ≠ 0) := by
  intro h
  have := certificate4449
  rw [h.1] at this
  norm_num at this
def C4450 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4450 : C4450.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4450 : ¬ (C4450.det = 0 ∧ ∀ i, C4450.adjugate i i ≠ 0) := by
  intro h
  have := certificate4450
  rw [h.1] at this
  norm_num at this
def C4451 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4451 : C4451.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4451 : ¬ (C4451.det = 0 ∧ ∀ i, C4451.adjugate i i ≠ 0) := by
  intro h
  have := certificate4451
  rw [h.1] at this
  norm_num at this
def C4452 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4452 : C4452.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4452 : ¬ (C4452.det = 0 ∧ ∀ i, C4452.adjugate i i ≠ 0) := by
  intro h
  have := certificate4452
  rw [h.1] at this
  norm_num at this
def C4453 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4453 : C4453.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4453 : ¬ (C4453.det = 0 ∧ ∀ i, C4453.adjugate i i ≠ 0) := by
  intro h
  have := certificate4453
  rw [h.1] at this
  norm_num at this
def C4454 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4454 : C4454.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4454 : ¬ (C4454.det = 0 ∧ ∀ i, C4454.adjugate i i ≠ 0) := by
  intro h
  have := certificate4454
  rw [h.1] at this
  norm_num at this
def C4455 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4455 : C4455.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4455 : ¬ (C4455.det = 0 ∧ ∀ i, C4455.adjugate i i ≠ 0) := by
  intro h
  have := certificate4455
  rw [h.1] at this
  norm_num at this
def C4456 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4456 : C4456.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4456 : ¬ (C4456.det = 0 ∧ ∀ i, C4456.adjugate i i ≠ 0) := by
  intro h
  have := certificate4456
  rw [h.1] at this
  norm_num at this
def C4457 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4457 : C4457.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4457 : ¬ (C4457.det = 0 ∧ ∀ i, C4457.adjugate i i ≠ 0) := by
  intro h
  have := certificate4457
  rw [h.1] at this
  norm_num at this
def C4458 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4458 : C4458.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4458 : ¬ (C4458.det = 0 ∧ ∀ i, C4458.adjugate i i ≠ 0) := by
  intro h
  have := certificate4458
  rw [h.1] at this
  norm_num at this
def C4459 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4459 : C4459.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4459 : ¬ (C4459.det = 0 ∧ ∀ i, C4459.adjugate i i ≠ 0) := by
  intro h
  have := certificate4459
  rw [h.1] at this
  norm_num at this
def C4460 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4460 : C4460.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4460 : ¬ (C4460.det = 0 ∧ ∀ i, C4460.adjugate i i ≠ 0) := by
  intro h
  have := certificate4460
  rw [h.1] at this
  norm_num at this
def C4461 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4461 : C4461.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4461 : ¬ (C4461.det = 0 ∧ ∀ i, C4461.adjugate i i ≠ 0) := by
  intro h
  have := certificate4461
  rw [h.1] at this
  norm_num at this
def C4462 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4462 : C4462.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4462 : ¬ (C4462.det = 0 ∧ ∀ i, C4462.adjugate i i ≠ 0) := by
  intro h
  have := certificate4462
  rw [h.1] at this
  norm_num at this
def C4463 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4463 : C4463.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4463 : ¬ (C4463.det = 0 ∧ ∀ i, C4463.adjugate i i ≠ 0) := by
  intro h
  have := certificate4463
  rw [h.1] at this
  norm_num at this
def C4464 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4464 : C4464.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4464 : ¬ (C4464.det = 0 ∧ ∀ i, C4464.adjugate i i ≠ 0) := by
  intro h
  have := certificate4464
  rw [h.1] at this
  norm_num at this
def C4465 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4465 : C4465.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4465 : ¬ (C4465.det = 0 ∧ ∀ i, C4465.adjugate i i ≠ 0) := by
  intro h
  have := certificate4465
  rw [h.1] at this
  norm_num at this
def C4466 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4466 : C4466.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4466 : ¬ (C4466.det = 0 ∧ ∀ i, C4466.adjugate i i ≠ 0) := by
  intro h
  have := certificate4466
  rw [h.1] at this
  norm_num at this
def C4467 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4467 : C4467.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4467 : ¬ (C4467.det = 0 ∧ ∀ i, C4467.adjugate i i ≠ 0) := by
  intro h
  have := certificate4467
  rw [h.1] at this
  norm_num at this
def C4468 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4468 : C4468.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4468 : ¬ (C4468.det = 0 ∧ ∀ i, C4468.adjugate i i ≠ 0) := by
  intro h
  have := certificate4468
  rw [h.1] at this
  norm_num at this
def C4469 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4469 : C4469.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4469 : ¬ (C4469.det = 0 ∧ ∀ i, C4469.adjugate i i ≠ 0) := by
  intro h
  have := certificate4469
  rw [h.1] at this
  norm_num at this
def C4470 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4470 : C4470.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4470 : ¬ (C4470.det = 0 ∧ ∀ i, C4470.adjugate i i ≠ 0) := by
  intro h
  have := certificate4470
  rw [h.1] at this
  norm_num at this
def C4471 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4471 : C4471.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4471 : ¬ (C4471.det = 0 ∧ ∀ i, C4471.adjugate i i ≠ 0) := by
  intro h
  have := certificate4471
  rw [h.1] at this
  norm_num at this
def C4472 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4472 : C4472.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4472 : ¬ (C4472.det = 0 ∧ ∀ i, C4472.adjugate i i ≠ 0) := by
  intro h
  have := certificate4472
  rw [h.1] at this
  norm_num at this
def C4473 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4473 : C4473.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4473 : ¬ (C4473.det = 0 ∧ ∀ i, C4473.adjugate i i ≠ 0) := by
  intro h
  have := certificate4473
  rw [h.1] at this
  norm_num at this
def C4474 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4474 : C4474.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4474 : ¬ (C4474.det = 0 ∧ ∀ i, C4474.adjugate i i ≠ 0) := by
  intro h
  have := certificate4474
  rw [h.1] at this
  norm_num at this
def C4475 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4475 : C4475.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4475 : ¬ (C4475.det = 0 ∧ ∀ i, C4475.adjugate i i ≠ 0) := by
  intro h
  have := certificate4475
  rw [h.1] at this
  norm_num at this
def C4476 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4476 : C4476.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4476 : ¬ (C4476.det = 0 ∧ ∀ i, C4476.adjugate i i ≠ 0) := by
  intro h
  have := certificate4476
  rw [h.1] at this
  norm_num at this
def C4477 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4477 : C4477.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4477 : ¬ (C4477.det = 0 ∧ ∀ i, C4477.adjugate i i ≠ 0) := by
  intro h
  have := certificate4477
  rw [h.1] at this
  norm_num at this
def C4478 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4478 : C4478.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4478 : ¬ (C4478.det = 0 ∧ ∀ i, C4478.adjugate i i ≠ 0) := by
  intro h
  have := certificate4478
  rw [h.1] at this
  norm_num at this
def C4479 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4479 : C4479.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4479 : ¬ (C4479.det = 0 ∧ ∀ i, C4479.adjugate i i ≠ 0) := by
  intro h
  have := certificate4479
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0139
