import VerifiedDet
namespace Nut8.NewCertificates0200
def C6400 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6400 : C6400.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6400 : ¬ (C6400.det = 0 ∧ ∀ i, C6400.adjugate i i ≠ 0) := by
  intro h
  have := certificate6400
  rw [h.1] at this
  norm_num at this
def C6401 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6401 : C6401.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6401 : ¬ (C6401.det = 0 ∧ ∀ i, C6401.adjugate i i ≠ 0) := by
  intro h
  have := certificate6401
  rw [h.1] at this
  norm_num at this
def C6402 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6402 : C6402.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6402 : ¬ (C6402.det = 0 ∧ ∀ i, C6402.adjugate i i ≠ 0) := by
  intro h
  have := certificate6402
  rw [h.1] at this
  norm_num at this
def C6403 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6403 : C6403.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6403 : ¬ (C6403.det = 0 ∧ ∀ i, C6403.adjugate i i ≠ 0) := by
  intro h
  have := certificate6403
  rw [h.1] at this
  norm_num at this
def C6404 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6404 : C6404.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6404 : ¬ (C6404.det = 0 ∧ ∀ i, C6404.adjugate i i ≠ 0) := by
  intro h
  have := certificate6404
  rw [h.1] at this
  norm_num at this
def C6405 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6405 : C6405.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6405 : ¬ (C6405.det = 0 ∧ ∀ i, C6405.adjugate i i ≠ 0) := by
  intro h
  have := certificate6405
  rw [h.1] at this
  norm_num at this
def C6406 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6406 : C6406.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6406 : ¬ (C6406.det = 0 ∧ ∀ i, C6406.adjugate i i ≠ 0) := by
  intro h
  have := certificate6406
  rw [h.1] at this
  norm_num at this
def C6407 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6407 : C6407.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6407 : ¬ (C6407.det = 0 ∧ ∀ i, C6407.adjugate i i ≠ 0) := by
  intro h
  have := certificate6407
  rw [h.1] at this
  norm_num at this
def C6408 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6408 : C6408.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6408 : ¬ (C6408.det = 0 ∧ ∀ i, C6408.adjugate i i ≠ 0) := by
  intro h
  have := certificate6408
  rw [h.1] at this
  norm_num at this
def C6409 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6409 : C6409.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6409 : ¬ (C6409.det = 0 ∧ ∀ i, C6409.adjugate i i ≠ 0) := by
  intro h
  have := certificate6409
  rw [h.1] at this
  norm_num at this
def C6410 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6410 : C6410.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6410 : ¬ (C6410.det = 0 ∧ ∀ i, C6410.adjugate i i ≠ 0) := by
  intro h
  have := certificate6410
  rw [h.1] at this
  norm_num at this
def C6411 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6411 : C6411.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6411 : ¬ (C6411.det = 0 ∧ ∀ i, C6411.adjugate i i ≠ 0) := by
  intro h
  have := certificate6411
  rw [h.1] at this
  norm_num at this
def C6412 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -2, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6412 : C6412.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6412 : ¬ (C6412.det = 0 ∧ ∀ i, C6412.adjugate i i ≠ 0) := by
  intro h
  have := certificate6412
  rw [h.1] at this
  norm_num at this
def C6413 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -2, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6413 : C6413.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6413 : ¬ (C6413.det = 0 ∧ ∀ i, C6413.adjugate i i ≠ 0) := by
  intro h
  have := certificate6413
  rw [h.1] at this
  norm_num at this
def C6414 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -2, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6414 : C6414.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6414 : ¬ (C6414.det = 0 ∧ ∀ i, C6414.adjugate i i ≠ 0) := by
  intro h
  have := certificate6414
  rw [h.1] at this
  norm_num at this
def C6415 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -2, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6415 : C6415.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6415 : ¬ (C6415.det = 0 ∧ ∀ i, C6415.adjugate i i ≠ 0) := by
  intro h
  have := certificate6415
  rw [h.1] at this
  norm_num at this
def C6416 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -2, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6416 : C6416.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6416 : ¬ (C6416.det = 0 ∧ ∀ i, C6416.adjugate i i ≠ 0) := by
  intro h
  have := certificate6416
  rw [h.1] at this
  norm_num at this
def C6417 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -2, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6417 : C6417.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6417 : ¬ (C6417.det = 0 ∧ ∀ i, C6417.adjugate i i ≠ 0) := by
  intro h
  have := certificate6417
  rw [h.1] at this
  norm_num at this
def C6418 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -2, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6418 : C6418.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6418 : ¬ (C6418.det = 0 ∧ ∀ i, C6418.adjugate i i ≠ 0) := by
  intro h
  have := certificate6418
  rw [h.1] at this
  norm_num at this
def C6419 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, -2, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6419 : C6419.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6419 : ¬ (C6419.det = 0 ∧ ∀ i, C6419.adjugate i i ≠ 0) := by
  intro h
  have := certificate6419
  rw [h.1] at this
  norm_num at this
def C6420 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6420 : C6420.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6420 : ¬ (C6420.det = 0 ∧ ∀ i, C6420.adjugate i i ≠ 0) := by
  intro h
  have := certificate6420
  rw [h.1] at this
  norm_num at this
def C6421 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6421 : C6421.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6421 : ¬ (C6421.det = 0 ∧ ∀ i, C6421.adjugate i i ≠ 0) := by
  intro h
  have := certificate6421
  rw [h.1] at this
  norm_num at this
def C6422 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6422 : C6422.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6422 : ¬ (C6422.det = 0 ∧ ∀ i, C6422.adjugate i i ≠ 0) := by
  intro h
  have := certificate6422
  rw [h.1] at this
  norm_num at this
def C6423 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6423 : C6423.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6423 : ¬ (C6423.det = 0 ∧ ∀ i, C6423.adjugate i i ≠ 0) := by
  intro h
  have := certificate6423
  rw [h.1] at this
  norm_num at this
def C6424 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6424 : C6424.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6424 : ¬ (C6424.det = 0 ∧ ∀ i, C6424.adjugate i i ≠ 0) := by
  intro h
  have := certificate6424
  rw [h.1] at this
  norm_num at this
def C6425 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6425 : C6425.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6425 : ¬ (C6425.det = 0 ∧ ∀ i, C6425.adjugate i i ≠ 0) := by
  intro h
  have := certificate6425
  rw [h.1] at this
  norm_num at this
def C6426 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6426 : C6426.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6426 : ¬ (C6426.det = 0 ∧ ∀ i, C6426.adjugate i i ≠ 0) := by
  intro h
  have := certificate6426
  rw [h.1] at this
  norm_num at this
def C6427 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6427 : C6427.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6427 : ¬ (C6427.det = 0 ∧ ∀ i, C6427.adjugate i i ≠ 0) := by
  intro h
  have := certificate6427
  rw [h.1] at this
  norm_num at this
def C6428 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6428 : C6428.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6428 : ¬ (C6428.det = 0 ∧ ∀ i, C6428.adjugate i i ≠ 0) := by
  intro h
  have := certificate6428
  rw [h.1] at this
  norm_num at this
def C6429 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6429 : C6429.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6429 : ¬ (C6429.det = 0 ∧ ∀ i, C6429.adjugate i i ≠ 0) := by
  intro h
  have := certificate6429
  rw [h.1] at this
  norm_num at this
def C6430 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6430 : C6430.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6430 : ¬ (C6430.det = 0 ∧ ∀ i, C6430.adjugate i i ≠ 0) := by
  intro h
  have := certificate6430
  rw [h.1] at this
  norm_num at this
def C6431 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6431 : C6431.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6431 : ¬ (C6431.det = 0 ∧ ∀ i, C6431.adjugate i i ≠ 0) := by
  intro h
  have := certificate6431
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0200
