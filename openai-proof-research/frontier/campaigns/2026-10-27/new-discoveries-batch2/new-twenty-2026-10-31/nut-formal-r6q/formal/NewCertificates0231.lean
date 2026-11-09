import VerifiedDet
namespace Nut8.NewCertificates0231
def C7392 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7392 : C7392.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7392 : ¬ (C7392.det = 0 ∧ ∀ i, C7392.adjugate i i ≠ 0) := by
  intro h
  have := certificate7392
  rw [h.1] at this
  norm_num at this
def C7393 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7393 : C7393.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7393 : ¬ (C7393.det = 0 ∧ ∀ i, C7393.adjugate i i ≠ 0) := by
  intro h
  have := certificate7393
  rw [h.1] at this
  norm_num at this
def C7394 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7394 : C7394.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7394 : ¬ (C7394.det = 0 ∧ ∀ i, C7394.adjugate i i ≠ 0) := by
  intro h
  have := certificate7394
  rw [h.1] at this
  norm_num at this
def C7395 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7395 : C7395.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7395 : ¬ (C7395.det = 0 ∧ ∀ i, C7395.adjugate i i ≠ 0) := by
  intro h
  have := certificate7395
  rw [h.1] at this
  norm_num at this
def C7396 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7396 : C7396.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7396 : ¬ (C7396.det = 0 ∧ ∀ i, C7396.adjugate i i ≠ 0) := by
  intro h
  have := certificate7396
  rw [h.1] at this
  norm_num at this
def C7397 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7397 : C7397.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7397 : ¬ (C7397.det = 0 ∧ ∀ i, C7397.adjugate i i ≠ 0) := by
  intro h
  have := certificate7397
  rw [h.1] at this
  norm_num at this
def C7398 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7398 : C7398.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7398 : ¬ (C7398.det = 0 ∧ ∀ i, C7398.adjugate i i ≠ 0) := by
  intro h
  have := certificate7398
  rw [h.1] at this
  norm_num at this
def C7399 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7399 : C7399.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7399 : ¬ (C7399.det = 0 ∧ ∀ i, C7399.adjugate i i ≠ 0) := by
  intro h
  have := certificate7399
  rw [h.1] at this
  norm_num at this
def C7400 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7400 : C7400.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7400 : ¬ (C7400.det = 0 ∧ ∀ i, C7400.adjugate i i ≠ 0) := by
  intro h
  have := certificate7400
  rw [h.1] at this
  norm_num at this
def C7401 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7401 : C7401.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7401 : ¬ (C7401.det = 0 ∧ ∀ i, C7401.adjugate i i ≠ 0) := by
  intro h
  have := certificate7401
  rw [h.1] at this
  norm_num at this
def C7402 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7402 : C7402.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7402 : ¬ (C7402.det = 0 ∧ ∀ i, C7402.adjugate i i ≠ 0) := by
  intro h
  have := certificate7402
  rw [h.1] at this
  norm_num at this
def C7403 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7403 : C7403.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7403 : ¬ (C7403.det = 0 ∧ ∀ i, C7403.adjugate i i ≠ 0) := by
  intro h
  have := certificate7403
  rw [h.1] at this
  norm_num at this
def C7404 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7404 : C7404.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7404 : ¬ (C7404.det = 0 ∧ ∀ i, C7404.adjugate i i ≠ 0) := by
  intro h
  have := certificate7404
  rw [h.1] at this
  norm_num at this
def C7405 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7405 : C7405.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7405 : ¬ (C7405.det = 0 ∧ ∀ i, C7405.adjugate i i ≠ 0) := by
  intro h
  have := certificate7405
  rw [h.1] at this
  norm_num at this
def C7406 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7406 : C7406.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7406 : ¬ (C7406.det = 0 ∧ ∀ i, C7406.adjugate i i ≠ 0) := by
  intro h
  have := certificate7406
  rw [h.1] at this
  norm_num at this
def C7407 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7407 : C7407.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7407 : ¬ (C7407.det = 0 ∧ ∀ i, C7407.adjugate i i ≠ 0) := by
  intro h
  have := certificate7407
  rw [h.1] at this
  norm_num at this
def C7408 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7408 : C7408.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7408 : ¬ (C7408.det = 0 ∧ ∀ i, C7408.adjugate i i ≠ 0) := by
  intro h
  have := certificate7408
  rw [h.1] at this
  norm_num at this
def C7409 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7409 : C7409.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7409 : ¬ (C7409.det = 0 ∧ ∀ i, C7409.adjugate i i ≠ 0) := by
  intro h
  have := certificate7409
  rw [h.1] at this
  norm_num at this
def C7410 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7410 : C7410.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7410 : ¬ (C7410.det = 0 ∧ ∀ i, C7410.adjugate i i ≠ 0) := by
  intro h
  have := certificate7410
  rw [h.1] at this
  norm_num at this
def C7411 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7411 : C7411.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7411 : ¬ (C7411.det = 0 ∧ ∀ i, C7411.adjugate i i ≠ 0) := by
  intro h
  have := certificate7411
  rw [h.1] at this
  norm_num at this
def C7412 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7412 : C7412.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7412 : ¬ (C7412.det = 0 ∧ ∀ i, C7412.adjugate i i ≠ 0) := by
  intro h
  have := certificate7412
  rw [h.1] at this
  norm_num at this
def C7413 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, 1, 0, 0]
theorem certificate7413 : C7413.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7413 : ¬ (C7413.det = 0 ∧ ∀ i, C7413.adjugate i i ≠ 0) := by
  intro h
  have := certificate7413
  rw [h.1] at this
  norm_num at this
def C7414 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7414 : C7414.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7414 : ¬ (C7414.det = 0 ∧ ∀ i, C7414.adjugate i i ≠ 0) := by
  intro h
  have := certificate7414
  rw [h.1] at this
  norm_num at this
def C7415 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, -1, 0, 0]
theorem certificate7415 : C7415.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7415 : ¬ (C7415.det = 0 ∧ ∀ i, C7415.adjugate i i ≠ 0) := by
  intro h
  have := certificate7415
  rw [h.1] at this
  norm_num at this
def C7416 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7416 : C7416.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7416 : ¬ (C7416.det = 0 ∧ ∀ i, C7416.adjugate i i ≠ 0) := by
  intro h
  have := certificate7416
  rw [h.1] at this
  norm_num at this
def C7417 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7417 : C7417.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7417 : ¬ (C7417.det = 0 ∧ ∀ i, C7417.adjugate i i ≠ 0) := by
  intro h
  have := certificate7417
  rw [h.1] at this
  norm_num at this
def C7418 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7418 : C7418.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7418 : ¬ (C7418.det = 0 ∧ ∀ i, C7418.adjugate i i ≠ 0) := by
  intro h
  have := certificate7418
  rw [h.1] at this
  norm_num at this
def C7419 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7419 : C7419.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7419 : ¬ (C7419.det = 0 ∧ ∀ i, C7419.adjugate i i ≠ 0) := by
  intro h
  have := certificate7419
  rw [h.1] at this
  norm_num at this
def C7420 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7420 : C7420.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7420 : ¬ (C7420.det = 0 ∧ ∀ i, C7420.adjugate i i ≠ 0) := by
  intro h
  have := certificate7420
  rw [h.1] at this
  norm_num at this
def C7421 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7421 : C7421.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7421 : ¬ (C7421.det = 0 ∧ ∀ i, C7421.adjugate i i ≠ 0) := by
  intro h
  have := certificate7421
  rw [h.1] at this
  norm_num at this
def C7422 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7422 : C7422.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7422 : ¬ (C7422.det = 0 ∧ ∀ i, C7422.adjugate i i ≠ 0) := by
  intro h
  have := certificate7422
  rw [h.1] at this
  norm_num at this
def C7423 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7423 : C7423.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7423 : ¬ (C7423.det = 0 ∧ ∀ i, C7423.adjugate i i ≠ 0) := by
  intro h
  have := certificate7423
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0231
