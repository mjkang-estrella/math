import VerifiedDet
namespace Nut8.NewCertificates0078
def C2496 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate2496 : C2496.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2496 : ¬ (C2496.det = 0 ∧ ∀ i, C2496.adjugate i i ≠ 0) := by
  intro h
  have := certificate2496
  rw [h.1] at this
  norm_num at this
def C2497 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate2497 : C2497.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2497 : ¬ (C2497.det = 0 ∧ ∀ i, C2497.adjugate i i ≠ 0) := by
  intro h
  have := certificate2497
  rw [h.1] at this
  norm_num at this
def C2498 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate2498 : C2498.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2498 : ¬ (C2498.det = 0 ∧ ∀ i, C2498.adjugate i i ≠ 0) := by
  intro h
  have := certificate2498
  rw [h.1] at this
  norm_num at this
def C2499 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate2499 : C2499.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2499 : ¬ (C2499.det = 0 ∧ ∀ i, C2499.adjugate i i ≠ 0) := by
  intro h
  have := certificate2499
  rw [h.1] at this
  norm_num at this
def C2500 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate2500 : C2500.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2500 : ¬ (C2500.det = 0 ∧ ∀ i, C2500.adjugate i i ≠ 0) := by
  intro h
  have := certificate2500
  rw [h.1] at this
  norm_num at this
def C2501 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate2501 : C2501.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2501 : ¬ (C2501.det = 0 ∧ ∀ i, C2501.adjugate i i ≠ 0) := by
  intro h
  have := certificate2501
  rw [h.1] at this
  norm_num at this
def C2502 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate2502 : C2502.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2502 : ¬ (C2502.det = 0 ∧ ∀ i, C2502.adjugate i i ≠ 0) := by
  intro h
  have := certificate2502
  rw [h.1] at this
  norm_num at this
def C2503 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate2503 : C2503.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2503 : ¬ (C2503.det = 0 ∧ ∀ i, C2503.adjugate i i ≠ 0) := by
  intro h
  have := certificate2503
  rw [h.1] at this
  norm_num at this
def C2504 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate2504 : C2504.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2504 : ¬ (C2504.det = 0 ∧ ∀ i, C2504.adjugate i i ≠ 0) := by
  intro h
  have := certificate2504
  rw [h.1] at this
  norm_num at this
def C2505 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate2505 : C2505.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2505 : ¬ (C2505.det = 0 ∧ ∀ i, C2505.adjugate i i ≠ 0) := by
  intro h
  have := certificate2505
  rw [h.1] at this
  norm_num at this
def C2506 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate2506 : C2506.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2506 : ¬ (C2506.det = 0 ∧ ∀ i, C2506.adjugate i i ≠ 0) := by
  intro h
  have := certificate2506
  rw [h.1] at this
  norm_num at this
def C2507 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate2507 : C2507.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2507 : ¬ (C2507.det = 0 ∧ ∀ i, C2507.adjugate i i ≠ 0) := by
  intro h
  have := certificate2507
  rw [h.1] at this
  norm_num at this
def C2508 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate2508 : C2508.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2508 : ¬ (C2508.det = 0 ∧ ∀ i, C2508.adjugate i i ≠ 0) := by
  intro h
  have := certificate2508
  rw [h.1] at this
  norm_num at this
def C2509 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate2509 : C2509.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2509 : ¬ (C2509.det = 0 ∧ ∀ i, C2509.adjugate i i ≠ 0) := by
  intro h
  have := certificate2509
  rw [h.1] at this
  norm_num at this
def C2510 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate2510 : C2510.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2510 : ¬ (C2510.det = 0 ∧ ∀ i, C2510.adjugate i i ≠ 0) := by
  intro h
  have := certificate2510
  rw [h.1] at this
  norm_num at this
def C2511 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate2511 : C2511.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2511 : ¬ (C2511.det = 0 ∧ ∀ i, C2511.adjugate i i ≠ 0) := by
  intro h
  have := certificate2511
  rw [h.1] at this
  norm_num at this
def C2512 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate2512 : C2512.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2512 : ¬ (C2512.det = 0 ∧ ∀ i, C2512.adjugate i i ≠ 0) := by
  intro h
  have := certificate2512
  rw [h.1] at this
  norm_num at this
def C2513 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate2513 : C2513.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2513 : ¬ (C2513.det = 0 ∧ ∀ i, C2513.adjugate i i ≠ 0) := by
  intro h
  have := certificate2513
  rw [h.1] at this
  norm_num at this
def C2514 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate2514 : C2514.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2514 : ¬ (C2514.det = 0 ∧ ∀ i, C2514.adjugate i i ≠ 0) := by
  intro h
  have := certificate2514
  rw [h.1] at this
  norm_num at this
def C2515 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate2515 : C2515.det = (37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2515 : ¬ (C2515.det = 0 ∧ ∀ i, C2515.adjugate i i ≠ 0) := by
  intro h
  have := certificate2515
  rw [h.1] at this
  norm_num at this
def C2516 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate2516 : C2516.det = (37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2516 : ¬ (C2516.det = 0 ∧ ∀ i, C2516.adjugate i i ≠ 0) := by
  intro h
  have := certificate2516
  rw [h.1] at this
  norm_num at this
def C2517 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate2517 : C2517.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2517 : ¬ (C2517.det = 0 ∧ ∀ i, C2517.adjugate i i ≠ 0) := by
  intro h
  have := certificate2517
  rw [h.1] at this
  norm_num at this
def C2518 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate2518 : C2518.det = (-91 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2518 : ¬ (C2518.det = 0 ∧ ∀ i, C2518.adjugate i i ≠ 0) := by
  intro h
  have := certificate2518
  rw [h.1] at this
  norm_num at this
def C2519 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate2519 : C2519.det = (109 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2519 : ¬ (C2519.det = 0 ∧ ∀ i, C2519.adjugate i i ≠ 0) := by
  intro h
  have := certificate2519
  rw [h.1] at this
  norm_num at this
def C2520 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate2520 : C2520.det = (109 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2520 : ¬ (C2520.det = 0 ∧ ∀ i, C2520.adjugate i i ≠ 0) := by
  intro h
  have := certificate2520
  rw [h.1] at this
  norm_num at this
def C2521 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate2521 : C2521.det = (-91 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2521 : ¬ (C2521.det = 0 ∧ ∀ i, C2521.adjugate i i ≠ 0) := by
  intro h
  have := certificate2521
  rw [h.1] at this
  norm_num at this
def C2522 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2522 : C2522.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2522 : ¬ (C2522.det = 0 ∧ ∀ i, C2522.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2522
def C2523 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2523 : C2523.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2523 : ¬ (C2523.det = 0 ∧ ∀ i, C2523.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2523
def C2524 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2524 : C2524.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2524 : ¬ (C2524.det = 0 ∧ ∀ i, C2524.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2524
def C2525 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2525 : C2525.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2525 : ¬ (C2525.det = 0 ∧ ∀ i, C2525.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2525
def C2526 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2526 : C2526.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2526 : ¬ (C2526.det = 0 ∧ ∀ i, C2526.adjugate i i ≠ 0) := by
  intro h
  have := certificate2526
  rw [h.1] at this
  norm_num at this
def C2527 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2527 : C2527.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2527 : ¬ (C2527.det = 0 ∧ ∀ i, C2527.adjugate i i ≠ 0) := by
  intro h
  have := certificate2527
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0078
