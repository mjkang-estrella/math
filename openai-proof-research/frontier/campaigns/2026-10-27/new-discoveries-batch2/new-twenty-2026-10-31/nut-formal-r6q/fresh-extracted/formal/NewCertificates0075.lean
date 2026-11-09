import VerifiedDet
namespace Nut8.NewCertificates0075
def C2400 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2400 : C2400.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2400 : ¬ (C2400.det = 0 ∧ ∀ i, C2400.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2400
def C2401 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2401 : C2401.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2401 : ¬ (C2401.det = 0 ∧ ∀ i, C2401.adjugate i i ≠ 0) := by
  intro h
  have := certificate2401
  rw [h.1] at this
  norm_num at this
def C2402 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2402 : C2402.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2402 : ¬ (C2402.det = 0 ∧ ∀ i, C2402.adjugate i i ≠ 0) := by
  intro h
  have := certificate2402
  rw [h.1] at this
  norm_num at this
def C2403 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2403 : C2403.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2403 : ¬ (C2403.det = 0 ∧ ∀ i, C2403.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2403
def C2404 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2404 : C2404.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2404 : ¬ (C2404.det = 0 ∧ ∀ i, C2404.adjugate i i ≠ 0) := by
  intro h
  have := certificate2404
  rw [h.1] at this
  norm_num at this
def C2405 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2405 : C2405.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2405 : ¬ (C2405.det = 0 ∧ ∀ i, C2405.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2405
def C2406 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2406 : C2406.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2406 : ¬ (C2406.det = 0 ∧ ∀ i, C2406.adjugate i i ≠ 0) := by
  intro h
  have := certificate2406
  rw [h.1] at this
  norm_num at this
def C2407 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2407 : C2407.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2407 : ¬ (C2407.det = 0 ∧ ∀ i, C2407.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2407
def C2408 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2408 : C2408.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2408 : ¬ (C2408.det = 0 ∧ ∀ i, C2408.adjugate i i ≠ 0) := by
  intro h
  have := certificate2408
  rw [h.1] at this
  norm_num at this
def C2409 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2409 : C2409.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2409 : ¬ (C2409.det = 0 ∧ ∀ i, C2409.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2409
def C2410 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2410 : C2410.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2410 : ¬ (C2410.det = 0 ∧ ∀ i, C2410.adjugate i i ≠ 0) := by
  intro h
  have := certificate2410
  rw [h.1] at this
  norm_num at this
def C2411 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2411 : C2411.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2411 : ¬ (C2411.det = 0 ∧ ∀ i, C2411.adjugate i i ≠ 0) := by
  intro h
  have := certificate2411
  rw [h.1] at this
  norm_num at this
def C2412 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2412 : C2412.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2412 : ¬ (C2412.det = 0 ∧ ∀ i, C2412.adjugate i i ≠ 0) := by
  intro h
  have := certificate2412
  rw [h.1] at this
  norm_num at this
def C2413 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2413 : C2413.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2413 : ¬ (C2413.det = 0 ∧ ∀ i, C2413.adjugate i i ≠ 0) := by
  intro h
  have := certificate2413
  rw [h.1] at this
  norm_num at this
def C2414 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2414 : C2414.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2414 : ¬ (C2414.det = 0 ∧ ∀ i, C2414.adjugate i i ≠ 0) := by
  intro h
  have := certificate2414
  rw [h.1] at this
  norm_num at this
def C2415 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2415 : C2415.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2415 : ¬ (C2415.det = 0 ∧ ∀ i, C2415.adjugate i i ≠ 0) := by
  intro h
  have := certificate2415
  rw [h.1] at this
  norm_num at this
def C2416 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2416 : C2416.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2416 : ¬ (C2416.det = 0 ∧ ∀ i, C2416.adjugate i i ≠ 0) := by
  intro h
  have := certificate2416
  rw [h.1] at this
  norm_num at this
def C2417 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2417 : C2417.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2417 : ¬ (C2417.det = 0 ∧ ∀ i, C2417.adjugate i i ≠ 0) := by
  intro h
  have := certificate2417
  rw [h.1] at this
  norm_num at this
def C2418 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2418 : C2418.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2418 : ¬ (C2418.det = 0 ∧ ∀ i, C2418.adjugate i i ≠ 0) := by
  intro h
  have := certificate2418
  rw [h.1] at this
  norm_num at this
def C2419 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2419 : C2419.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2419 : ¬ (C2419.det = 0 ∧ ∀ i, C2419.adjugate i i ≠ 0) := by
  intro h
  have := certificate2419
  rw [h.1] at this
  norm_num at this
def C2420 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2420 : C2420.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2420 : ¬ (C2420.det = 0 ∧ ∀ i, C2420.adjugate i i ≠ 0) := by
  intro h
  have := certificate2420
  rw [h.1] at this
  norm_num at this
def C2421 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2421 : C2421.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2421 : ¬ (C2421.det = 0 ∧ ∀ i, C2421.adjugate i i ≠ 0) := by
  intro h
  have := certificate2421
  rw [h.1] at this
  norm_num at this
def C2422 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2422 : C2422.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2422 : ¬ (C2422.det = 0 ∧ ∀ i, C2422.adjugate i i ≠ 0) := by
  intro h
  have := certificate2422
  rw [h.1] at this
  norm_num at this
def C2423 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2423 : C2423.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2423 : ¬ (C2423.det = 0 ∧ ∀ i, C2423.adjugate i i ≠ 0) := by
  intro h
  have := certificate2423
  rw [h.1] at this
  norm_num at this
def C2424 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2424 : C2424.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2424 : ¬ (C2424.det = 0 ∧ ∀ i, C2424.adjugate i i ≠ 0) := by
  intro h
  have := certificate2424
  rw [h.1] at this
  norm_num at this
def C2425 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2425 : C2425.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2425 : ¬ (C2425.det = 0 ∧ ∀ i, C2425.adjugate i i ≠ 0) := by
  intro h
  have := certificate2425
  rw [h.1] at this
  norm_num at this
def C2426 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2426 : C2426.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2426 : ¬ (C2426.det = 0 ∧ ∀ i, C2426.adjugate i i ≠ 0) := by
  intro h
  have := certificate2426
  rw [h.1] at this
  norm_num at this
def C2427 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2427 : C2427.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2427 : ¬ (C2427.det = 0 ∧ ∀ i, C2427.adjugate i i ≠ 0) := by
  intro h
  have := certificate2427
  rw [h.1] at this
  norm_num at this
def C2428 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2428 : C2428.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2428 : ¬ (C2428.det = 0 ∧ ∀ i, C2428.adjugate i i ≠ 0) := by
  intro h
  have := certificate2428
  rw [h.1] at this
  norm_num at this
def C2429 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2429 : C2429.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2429 : ¬ (C2429.det = 0 ∧ ∀ i, C2429.adjugate i i ≠ 0) := by
  intro h
  have := certificate2429
  rw [h.1] at this
  norm_num at this
def C2430 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2430 : C2430.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2430 : ¬ (C2430.det = 0 ∧ ∀ i, C2430.adjugate i i ≠ 0) := by
  intro h
  have := certificate2430
  rw [h.1] at this
  norm_num at this
def C2431 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2431 : C2431.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2431 : ¬ (C2431.det = 0 ∧ ∀ i, C2431.adjugate i i ≠ 0) := by
  intro h
  have := certificate2431
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0075
