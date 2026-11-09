import VerifiedDet
namespace Nut8.NewCertificates0077
def C2464 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2464 : C2464.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2464 : ¬ (C2464.det = 0 ∧ ∀ i, C2464.adjugate i i ≠ 0) := by
  intro h
  have := certificate2464
  rw [h.1] at this
  norm_num at this
def C2465 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2465 : C2465.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2465 : ¬ (C2465.det = 0 ∧ ∀ i, C2465.adjugate i i ≠ 0) := by
  intro h
  have := certificate2465
  rw [h.1] at this
  norm_num at this
def C2466 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2466 : C2466.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2466 : ¬ (C2466.det = 0 ∧ ∀ i, C2466.adjugate i i ≠ 0) := by
  intro h
  have := certificate2466
  rw [h.1] at this
  norm_num at this
def C2467 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2467 : C2467.det = (49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2467 : ¬ (C2467.det = 0 ∧ ∀ i, C2467.adjugate i i ≠ 0) := by
  intro h
  have := certificate2467
  rw [h.1] at this
  norm_num at this
def C2468 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2468 : C2468.det = (81 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2468 : ¬ (C2468.det = 0 ∧ ∀ i, C2468.adjugate i i ≠ 0) := by
  intro h
  have := certificate2468
  rw [h.1] at this
  norm_num at this
def C2469 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2469 : C2469.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2469 : ¬ (C2469.det = 0 ∧ ∀ i, C2469.adjugate i i ≠ 0) := by
  intro h
  have := certificate2469
  rw [h.1] at this
  norm_num at this
def C2470 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2470 : C2470.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2470 : ¬ (C2470.det = 0 ∧ ∀ i, C2470.adjugate i i ≠ 0) := by
  intro h
  have := certificate2470
  rw [h.1] at this
  norm_num at this
def C2471 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2471 : C2471.det = (81 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2471 : ¬ (C2471.det = 0 ∧ ∀ i, C2471.adjugate i i ≠ 0) := by
  intro h
  have := certificate2471
  rw [h.1] at this
  norm_num at this
def C2472 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2472 : C2472.det = (49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2472 : ¬ (C2472.det = 0 ∧ ∀ i, C2472.adjugate i i ≠ 0) := by
  intro h
  have := certificate2472
  rw [h.1] at this
  norm_num at this
def C2473 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2473 : C2473.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2473 : ¬ (C2473.det = 0 ∧ ∀ i, C2473.adjugate i i ≠ 0) := by
  intro h
  have := certificate2473
  rw [h.1] at this
  norm_num at this
def C2474 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate2474 : C2474.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2474 : ¬ (C2474.det = 0 ∧ ∀ i, C2474.adjugate i i ≠ 0) := by
  intro h
  have := certificate2474
  rw [h.1] at this
  norm_num at this
def C2475 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate2475 : C2475.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2475 : ¬ (C2475.det = 0 ∧ ∀ i, C2475.adjugate i i ≠ 0) := by
  intro h
  have := certificate2475
  rw [h.1] at this
  norm_num at this
def C2476 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate2476 : C2476.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2476 : ¬ (C2476.det = 0 ∧ ∀ i, C2476.adjugate i i ≠ 0) := by
  intro h
  have := certificate2476
  rw [h.1] at this
  norm_num at this
def C2477 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate2477 : C2477.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2477 : ¬ (C2477.det = 0 ∧ ∀ i, C2477.adjugate i i ≠ 0) := by
  intro h
  have := certificate2477
  rw [h.1] at this
  norm_num at this
def C2478 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate2478 : C2478.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2478 : ¬ (C2478.det = 0 ∧ ∀ i, C2478.adjugate i i ≠ 0) := by
  intro h
  have := certificate2478
  rw [h.1] at this
  norm_num at this
def C2479 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate2479 : C2479.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2479 : ¬ (C2479.det = 0 ∧ ∀ i, C2479.adjugate i i ≠ 0) := by
  intro h
  have := certificate2479
  rw [h.1] at this
  norm_num at this
def C2480 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate2480 : C2480.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2480 : ¬ (C2480.det = 0 ∧ ∀ i, C2480.adjugate i i ≠ 0) := by
  intro h
  have := certificate2480
  rw [h.1] at this
  norm_num at this
def C2481 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate2481 : C2481.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2481 : ¬ (C2481.det = 0 ∧ ∀ i, C2481.adjugate i i ≠ 0) := by
  intro h
  have := certificate2481
  rw [h.1] at this
  norm_num at this
def C2482 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate2482 : C2482.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2482 : ¬ (C2482.det = 0 ∧ ∀ i, C2482.adjugate i i ≠ 0) := by
  intro h
  have := certificate2482
  rw [h.1] at this
  norm_num at this
def C2483 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate2483 : C2483.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2483 : ¬ (C2483.det = 0 ∧ ∀ i, C2483.adjugate i i ≠ 0) := by
  intro h
  have := certificate2483
  rw [h.1] at this
  norm_num at this
def C2484 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate2484 : C2484.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2484 : ¬ (C2484.det = 0 ∧ ∀ i, C2484.adjugate i i ≠ 0) := by
  intro h
  have := certificate2484
  rw [h.1] at this
  norm_num at this
def C2485 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate2485 : C2485.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2485 : ¬ (C2485.det = 0 ∧ ∀ i, C2485.adjugate i i ≠ 0) := by
  intro h
  have := certificate2485
  rw [h.1] at this
  norm_num at this
def C2486 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate2486 : C2486.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2486 : ¬ (C2486.det = 0 ∧ ∀ i, C2486.adjugate i i ≠ 0) := by
  intro h
  have := certificate2486
  rw [h.1] at this
  norm_num at this
def C2487 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate2487 : C2487.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2487 : ¬ (C2487.det = 0 ∧ ∀ i, C2487.adjugate i i ≠ 0) := by
  intro h
  have := certificate2487
  rw [h.1] at this
  norm_num at this
def C2488 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate2488 : C2488.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2488 : ¬ (C2488.det = 0 ∧ ∀ i, C2488.adjugate i i ≠ 0) := by
  intro h
  have := certificate2488
  rw [h.1] at this
  norm_num at this
def C2489 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate2489 : C2489.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2489 : ¬ (C2489.det = 0 ∧ ∀ i, C2489.adjugate i i ≠ 0) := by
  intro h
  have := certificate2489
  rw [h.1] at this
  norm_num at this
def C2490 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate2490 : C2490.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2490 : ¬ (C2490.det = 0 ∧ ∀ i, C2490.adjugate i i ≠ 0) := by
  intro h
  have := certificate2490
  rw [h.1] at this
  norm_num at this
def C2491 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate2491 : C2491.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2491 : ¬ (C2491.det = 0 ∧ ∀ i, C2491.adjugate i i ≠ 0) := by
  intro h
  have := certificate2491
  rw [h.1] at this
  norm_num at this
def C2492 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate2492 : C2492.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2492 : ¬ (C2492.det = 0 ∧ ∀ i, C2492.adjugate i i ≠ 0) := by
  intro h
  have := certificate2492
  rw [h.1] at this
  norm_num at this
def C2493 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate2493 : C2493.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2493 : ¬ (C2493.det = 0 ∧ ∀ i, C2493.adjugate i i ≠ 0) := by
  intro h
  have := certificate2493
  rw [h.1] at this
  norm_num at this
def C2494 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate2494 : C2494.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2494 : ¬ (C2494.det = 0 ∧ ∀ i, C2494.adjugate i i ≠ 0) := by
  intro h
  have := certificate2494
  rw [h.1] at this
  norm_num at this
def C2495 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate2495 : C2495.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2495 : ¬ (C2495.det = 0 ∧ ∀ i, C2495.adjugate i i ≠ 0) := by
  intro h
  have := certificate2495
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0077
