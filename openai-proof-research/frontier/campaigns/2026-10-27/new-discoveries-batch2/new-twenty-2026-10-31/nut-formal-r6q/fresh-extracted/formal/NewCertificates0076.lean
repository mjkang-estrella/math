import VerifiedDet
namespace Nut8.NewCertificates0076
def C2432 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2432 : C2432.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2432 : ¬ (C2432.det = 0 ∧ ∀ i, C2432.adjugate i i ≠ 0) := by
  intro h
  have := certificate2432
  rw [h.1] at this
  norm_num at this
def C2433 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2433 : C2433.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2433 : ¬ (C2433.det = 0 ∧ ∀ i, C2433.adjugate i i ≠ 0) := by
  intro h
  have := certificate2433
  rw [h.1] at this
  norm_num at this
def C2434 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2434 : C2434.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2434 : ¬ (C2434.det = 0 ∧ ∀ i, C2434.adjugate i i ≠ 0) := by
  intro h
  have := certificate2434
  rw [h.1] at this
  norm_num at this
def C2435 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2435 : C2435.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2435 : ¬ (C2435.det = 0 ∧ ∀ i, C2435.adjugate i i ≠ 0) := by
  intro h
  have := certificate2435
  rw [h.1] at this
  norm_num at this
def C2436 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2436 : C2436.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2436 : ¬ (C2436.det = 0 ∧ ∀ i, C2436.adjugate i i ≠ 0) := by
  intro h
  have := certificate2436
  rw [h.1] at this
  norm_num at this
def C2437 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2437 : C2437.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2437 : ¬ (C2437.det = 0 ∧ ∀ i, C2437.adjugate i i ≠ 0) := by
  intro h
  have := certificate2437
  rw [h.1] at this
  norm_num at this
def C2438 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2438 : C2438.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2438 : ¬ (C2438.det = 0 ∧ ∀ i, C2438.adjugate i i ≠ 0) := by
  intro h
  have := certificate2438
  rw [h.1] at this
  norm_num at this
def C2439 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2439 : C2439.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2439 : ¬ (C2439.det = 0 ∧ ∀ i, C2439.adjugate i i ≠ 0) := by
  intro h
  have := certificate2439
  rw [h.1] at this
  norm_num at this
def C2440 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2440 : C2440.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2440 : ¬ (C2440.det = 0 ∧ ∀ i, C2440.adjugate i i ≠ 0) := by
  intro h
  have := certificate2440
  rw [h.1] at this
  norm_num at this
def C2441 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2441 : C2441.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2441 : ¬ (C2441.det = 0 ∧ ∀ i, C2441.adjugate i i ≠ 0) := by
  intro h
  have := certificate2441
  rw [h.1] at this
  norm_num at this
def C2442 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2442 : C2442.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2442 : ¬ (C2442.det = 0 ∧ ∀ i, C2442.adjugate i i ≠ 0) := by
  intro h
  have := certificate2442
  rw [h.1] at this
  norm_num at this
def C2443 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2443 : C2443.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2443 : ¬ (C2443.det = 0 ∧ ∀ i, C2443.adjugate i i ≠ 0) := by
  intro h
  have := certificate2443
  rw [h.1] at this
  norm_num at this
def C2444 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2444 : C2444.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2444 : ¬ (C2444.det = 0 ∧ ∀ i, C2444.adjugate i i ≠ 0) := by
  intro h
  have := certificate2444
  rw [h.1] at this
  norm_num at this
def C2445 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2445 : C2445.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2445 : ¬ (C2445.det = 0 ∧ ∀ i, C2445.adjugate i i ≠ 0) := by
  intro h
  have := certificate2445
  rw [h.1] at this
  norm_num at this
def C2446 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2446 : C2446.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2446 : ¬ (C2446.det = 0 ∧ ∀ i, C2446.adjugate i i ≠ 0) := by
  intro h
  have := certificate2446
  rw [h.1] at this
  norm_num at this
def C2447 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2447 : C2447.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2447 : ¬ (C2447.det = 0 ∧ ∀ i, C2447.adjugate i i ≠ 0) := by
  intro h
  have := certificate2447
  rw [h.1] at this
  norm_num at this
def C2448 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2448 : C2448.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2448 : ¬ (C2448.det = 0 ∧ ∀ i, C2448.adjugate i i ≠ 0) := by
  intro h
  have := certificate2448
  rw [h.1] at this
  norm_num at this
def C2449 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2449 : C2449.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2449 : ¬ (C2449.det = 0 ∧ ∀ i, C2449.adjugate i i ≠ 0) := by
  intro h
  have := certificate2449
  rw [h.1] at this
  norm_num at this
def C2450 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2450 : C2450.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2450 : ¬ (C2450.det = 0 ∧ ∀ i, C2450.adjugate i i ≠ 0) := by
  intro h
  have := certificate2450
  rw [h.1] at this
  norm_num at this
def C2451 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2451 : C2451.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2451 : ¬ (C2451.det = 0 ∧ ∀ i, C2451.adjugate i i ≠ 0) := by
  intro h
  have := certificate2451
  rw [h.1] at this
  norm_num at this
def C2452 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2452 : C2452.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2452 : ¬ (C2452.det = 0 ∧ ∀ i, C2452.adjugate i i ≠ 0) := by
  intro h
  have := certificate2452
  rw [h.1] at this
  norm_num at this
def C2453 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2453 : C2453.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2453 : ¬ (C2453.det = 0 ∧ ∀ i, C2453.adjugate i i ≠ 0) := by
  intro h
  have := certificate2453
  rw [h.1] at this
  norm_num at this
def C2454 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2454 : C2454.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2454 : ¬ (C2454.det = 0 ∧ ∀ i, C2454.adjugate i i ≠ 0) := by
  intro h
  have := certificate2454
  rw [h.1] at this
  norm_num at this
def C2455 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2455 : C2455.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2455 : ¬ (C2455.det = 0 ∧ ∀ i, C2455.adjugate i i ≠ 0) := by
  intro h
  have := certificate2455
  rw [h.1] at this
  norm_num at this
def C2456 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2456 : C2456.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2456 : ¬ (C2456.det = 0 ∧ ∀ i, C2456.adjugate i i ≠ 0) := by
  intro h
  have := certificate2456
  rw [h.1] at this
  norm_num at this
def C2457 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2457 : C2457.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2457 : ¬ (C2457.det = 0 ∧ ∀ i, C2457.adjugate i i ≠ 0) := by
  intro h
  have := certificate2457
  rw [h.1] at this
  norm_num at this
def C2458 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2458 : C2458.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2458 : ¬ (C2458.det = 0 ∧ ∀ i, C2458.adjugate i i ≠ 0) := by
  intro h
  have := certificate2458
  rw [h.1] at this
  norm_num at this
def C2459 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2459 : C2459.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2459 : ¬ (C2459.det = 0 ∧ ∀ i, C2459.adjugate i i ≠ 0) := by
  intro h
  have := certificate2459
  rw [h.1] at this
  norm_num at this
def C2460 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2460 : C2460.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2460 : ¬ (C2460.det = 0 ∧ ∀ i, C2460.adjugate i i ≠ 0) := by
  intro h
  have := certificate2460
  rw [h.1] at this
  norm_num at this
def C2461 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2461 : C2461.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2461 : ¬ (C2461.det = 0 ∧ ∀ i, C2461.adjugate i i ≠ 0) := by
  intro h
  have := certificate2461
  rw [h.1] at this
  norm_num at this
def C2462 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2462 : C2462.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2462 : ¬ (C2462.det = 0 ∧ ∀ i, C2462.adjugate i i ≠ 0) := by
  intro h
  have := certificate2462
  rw [h.1] at this
  norm_num at this
def C2463 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2463 : C2463.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2463 : ¬ (C2463.det = 0 ∧ ∀ i, C2463.adjugate i i ≠ 0) := by
  intro h
  have := certificate2463
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0076
