import VerifiedDet
namespace Nut8.NewCertificates0013
def C416 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate416 : C416.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction416 : ¬ (C416.det = 0 ∧ ∀ i, C416.adjugate i i ≠ 0) := by
  intro h
  have := certificate416
  rw [h.1] at this
  norm_num at this
def C417 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate417 : C417.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction417 : ¬ (C417.det = 0 ∧ ∀ i, C417.adjugate i i ≠ 0) := by
  intro h
  have := certificate417
  rw [h.1] at this
  norm_num at this
def C418 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate418 : C418.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction418 : ¬ (C418.det = 0 ∧ ∀ i, C418.adjugate i i ≠ 0) := by
  intro h
  have := certificate418
  rw [h.1] at this
  norm_num at this
def C419 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate419 : C419.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction419 : ¬ (C419.det = 0 ∧ ∀ i, C419.adjugate i i ≠ 0) := by
  intro h
  have := certificate419
  rw [h.1] at this
  norm_num at this
def C420 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate420 : C420.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction420 : ¬ (C420.det = 0 ∧ ∀ i, C420.adjugate i i ≠ 0) := by
  intro h
  have := certificate420
  rw [h.1] at this
  norm_num at this
def C421 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate421 : C421.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction421 : ¬ (C421.det = 0 ∧ ∀ i, C421.adjugate i i ≠ 0) := by
  intro h
  have := certificate421
  rw [h.1] at this
  norm_num at this
def C422 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate422 : C422.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction422 : ¬ (C422.det = 0 ∧ ∀ i, C422.adjugate i i ≠ 0) := by
  intro h
  have := certificate422
  rw [h.1] at this
  norm_num at this
def C423 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate423 : C423.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction423 : ¬ (C423.det = 0 ∧ ∀ i, C423.adjugate i i ≠ 0) := by
  intro h
  have := certificate423
  rw [h.1] at this
  norm_num at this
def C424 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate424 : C424.det = (-88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction424 : ¬ (C424.det = 0 ∧ ∀ i, C424.adjugate i i ≠ 0) := by
  intro h
  have := certificate424
  rw [h.1] at this
  norm_num at this
def C425 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate425 : C425.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction425 : ¬ (C425.det = 0 ∧ ∀ i, C425.adjugate i i ≠ 0) := by
  intro h
  have := certificate425
  rw [h.1] at this
  norm_num at this
def C426 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate426 : C426.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction426 : ¬ (C426.det = 0 ∧ ∀ i, C426.adjugate i i ≠ 0) := by
  intro h
  have := certificate426
  rw [h.1] at this
  norm_num at this
def C427 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate427 : C427.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction427 : ¬ (C427.det = 0 ∧ ∀ i, C427.adjugate i i ≠ 0) := by
  intro h
  have := certificate427
  rw [h.1] at this
  norm_num at this
def C428 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate428 : C428.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction428 : ¬ (C428.det = 0 ∧ ∀ i, C428.adjugate i i ≠ 0) := by
  intro h
  have := certificate428
  rw [h.1] at this
  norm_num at this
def C429 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate429 : C429.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction429 : ¬ (C429.det = 0 ∧ ∀ i, C429.adjugate i i ≠ 0) := by
  intro h
  have := certificate429
  rw [h.1] at this
  norm_num at this
def C430 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate430 : C430.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction430 : ¬ (C430.det = 0 ∧ ∀ i, C430.adjugate i i ≠ 0) := by
  intro h
  have := certificate430
  rw [h.1] at this
  norm_num at this
def C431 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate431 : C431.det = (-88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction431 : ¬ (C431.det = 0 ∧ ∀ i, C431.adjugate i i ≠ 0) := by
  intro h
  have := certificate431
  rw [h.1] at this
  norm_num at this
def C432 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate432 : C432.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction432 : ¬ (C432.det = 0 ∧ ∀ i, C432.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate432
def C433 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate433 : C433.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction433 : ¬ (C433.det = 0 ∧ ∀ i, C433.adjugate i i ≠ 0) := by
  intro h
  have := certificate433
  rw [h.1] at this
  norm_num at this
def C434 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate434 : C434.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction434 : ¬ (C434.det = 0 ∧ ∀ i, C434.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate434
def C435 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate435 : C435.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction435 : ¬ (C435.det = 0 ∧ ∀ i, C435.adjugate i i ≠ 0) := by
  intro h
  have := certificate435
  rw [h.1] at this
  norm_num at this
def C436 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate436 : C436.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction436 : ¬ (C436.det = 0 ∧ ∀ i, C436.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate436
def C437 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate437 : C437.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction437 : ¬ (C437.det = 0 ∧ ∀ i, C437.adjugate i i ≠ 0) := by
  intro h
  have := certificate437
  rw [h.1] at this
  norm_num at this
def C438 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate438 : C438.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction438 : ¬ (C438.det = 0 ∧ ∀ i, C438.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate438
def C439 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate439 : C439.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction439 : ¬ (C439.det = 0 ∧ ∀ i, C439.adjugate i i ≠ 0) := by
  intro h
  have := certificate439
  rw [h.1] at this
  norm_num at this
def C440 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate440 : C440.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction440 : ¬ (C440.det = 0 ∧ ∀ i, C440.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate440
def C441 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate441 : C441.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction441 : ¬ (C441.det = 0 ∧ ∀ i, C441.adjugate i i ≠ 0) := by
  intro h
  have := certificate441
  rw [h.1] at this
  norm_num at this
def C442 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate442 : C442.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction442 : ¬ (C442.det = 0 ∧ ∀ i, C442.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate442
def C443 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate443 : C443.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction443 : ¬ (C443.det = 0 ∧ ∀ i, C443.adjugate i i ≠ 0) := by
  intro h
  have := certificate443
  rw [h.1] at this
  norm_num at this
def C444 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate444 : C444.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction444 : ¬ (C444.det = 0 ∧ ∀ i, C444.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate444
def C445 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate445 : C445.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction445 : ¬ (C445.det = 0 ∧ ∀ i, C445.adjugate i i ≠ 0) := by
  intro h
  have := certificate445
  rw [h.1] at this
  norm_num at this
def C446 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate446 : C446.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction446 : ¬ (C446.det = 0 ∧ ∀ i, C446.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate446
def C447 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate447 : C447.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction447 : ¬ (C447.det = 0 ∧ ∀ i, C447.adjugate i i ≠ 0) := by
  intro h
  have := certificate447
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0013
