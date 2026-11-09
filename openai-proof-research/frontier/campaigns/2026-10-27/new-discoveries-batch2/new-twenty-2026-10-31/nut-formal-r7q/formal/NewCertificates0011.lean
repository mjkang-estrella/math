import VerifiedDet
namespace Nut8.NewCertificates0011
def C352 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate352 : C352.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction352 : ¬ (C352.det = 0 ∧ ∀ i, C352.adjugate i i ≠ 0) := by
  intro h
  have := certificate352
  rw [h.1] at this
  norm_num at this
def C353 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate353 : C353.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction353 : ¬ (C353.det = 0 ∧ ∀ i, C353.adjugate i i ≠ 0) := by
  intro h
  have := certificate353
  rw [h.1] at this
  norm_num at this
def C354 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate354 : C354.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction354 : ¬ (C354.det = 0 ∧ ∀ i, C354.adjugate i i ≠ 0) := by
  intro h
  have := certificate354
  rw [h.1] at this
  norm_num at this
def C355 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate355 : C355.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction355 : ¬ (C355.det = 0 ∧ ∀ i, C355.adjugate i i ≠ 0) := by
  intro h
  have := certificate355
  rw [h.1] at this
  norm_num at this
def C356 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate356 : C356.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction356 : ¬ (C356.det = 0 ∧ ∀ i, C356.adjugate i i ≠ 0) := by
  intro h
  have := certificate356
  rw [h.1] at this
  norm_num at this
def C357 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate357 : C357.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction357 : ¬ (C357.det = 0 ∧ ∀ i, C357.adjugate i i ≠ 0) := by
  intro h
  have := certificate357
  rw [h.1] at this
  norm_num at this
def C358 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate358 : C358.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction358 : ¬ (C358.det = 0 ∧ ∀ i, C358.adjugate i i ≠ 0) := by
  intro h
  have := certificate358
  rw [h.1] at this
  norm_num at this
def C359 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate359 : C359.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction359 : ¬ (C359.det = 0 ∧ ∀ i, C359.adjugate i i ≠ 0) := by
  intro h
  have := certificate359
  rw [h.1] at this
  norm_num at this
def C360 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate360 : C360.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction360 : ¬ (C360.det = 0 ∧ ∀ i, C360.adjugate i i ≠ 0) := by
  intro h
  have := certificate360
  rw [h.1] at this
  norm_num at this
def C361 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate361 : C361.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction361 : ¬ (C361.det = 0 ∧ ∀ i, C361.adjugate i i ≠ 0) := by
  intro h
  have := certificate361
  rw [h.1] at this
  norm_num at this
def C362 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate362 : C362.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction362 : ¬ (C362.det = 0 ∧ ∀ i, C362.adjugate i i ≠ 0) := by
  intro h
  have := certificate362
  rw [h.1] at this
  norm_num at this
def C363 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate363 : C363.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction363 : ¬ (C363.det = 0 ∧ ∀ i, C363.adjugate i i ≠ 0) := by
  intro h
  have := certificate363
  rw [h.1] at this
  norm_num at this
def C364 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate364 : C364.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction364 : ¬ (C364.det = 0 ∧ ∀ i, C364.adjugate i i ≠ 0) := by
  intro h
  have := certificate364
  rw [h.1] at this
  norm_num at this
def C365 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate365 : C365.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction365 : ¬ (C365.det = 0 ∧ ∀ i, C365.adjugate i i ≠ 0) := by
  intro h
  have := certificate365
  rw [h.1] at this
  norm_num at this
def C366 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate366 : C366.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction366 : ¬ (C366.det = 0 ∧ ∀ i, C366.adjugate i i ≠ 0) := by
  intro h
  have := certificate366
  rw [h.1] at this
  norm_num at this
def C367 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate367 : C367.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction367 : ¬ (C367.det = 0 ∧ ∀ i, C367.adjugate i i ≠ 0) := by
  intro h
  have := certificate367
  rw [h.1] at this
  norm_num at this
def C368 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate368 : C368.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction368 : ¬ (C368.det = 0 ∧ ∀ i, C368.adjugate i i ≠ 0) := by
  intro h
  have := certificate368
  rw [h.1] at this
  norm_num at this
def C369 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate369 : C369.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction369 : ¬ (C369.det = 0 ∧ ∀ i, C369.adjugate i i ≠ 0) := by
  intro h
  have := certificate369
  rw [h.1] at this
  norm_num at this
def C370 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate370 : C370.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction370 : ¬ (C370.det = 0 ∧ ∀ i, C370.adjugate i i ≠ 0) := by
  intro h
  have := certificate370
  rw [h.1] at this
  norm_num at this
def C371 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate371 : C371.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction371 : ¬ (C371.det = 0 ∧ ∀ i, C371.adjugate i i ≠ 0) := by
  intro h
  have := certificate371
  rw [h.1] at this
  norm_num at this
def C372 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate372 : C372.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction372 : ¬ (C372.det = 0 ∧ ∀ i, C372.adjugate i i ≠ 0) := by
  intro h
  have := certificate372
  rw [h.1] at this
  norm_num at this
def C373 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate373 : C373.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction373 : ¬ (C373.det = 0 ∧ ∀ i, C373.adjugate i i ≠ 0) := by
  intro h
  have := certificate373
  rw [h.1] at this
  norm_num at this
def C374 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate374 : C374.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction374 : ¬ (C374.det = 0 ∧ ∀ i, C374.adjugate i i ≠ 0) := by
  intro h
  have := certificate374
  rw [h.1] at this
  norm_num at this
def C375 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate375 : C375.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction375 : ¬ (C375.det = 0 ∧ ∀ i, C375.adjugate i i ≠ 0) := by
  intro h
  have := certificate375
  rw [h.1] at this
  norm_num at this
def C376 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate376 : C376.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction376 : ¬ (C376.det = 0 ∧ ∀ i, C376.adjugate i i ≠ 0) := by
  intro h
  have := certificate376
  rw [h.1] at this
  norm_num at this
def C377 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate377 : C377.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction377 : ¬ (C377.det = 0 ∧ ∀ i, C377.adjugate i i ≠ 0) := by
  intro h
  have := certificate377
  rw [h.1] at this
  norm_num at this
def C378 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate378 : C378.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction378 : ¬ (C378.det = 0 ∧ ∀ i, C378.adjugate i i ≠ 0) := by
  intro h
  have := certificate378
  rw [h.1] at this
  norm_num at this
def C379 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate379 : C379.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction379 : ¬ (C379.det = 0 ∧ ∀ i, C379.adjugate i i ≠ 0) := by
  intro h
  have := certificate379
  rw [h.1] at this
  norm_num at this
def C380 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate380 : C380.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction380 : ¬ (C380.det = 0 ∧ ∀ i, C380.adjugate i i ≠ 0) := by
  intro h
  have := certificate380
  rw [h.1] at this
  norm_num at this
def C381 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate381 : C381.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction381 : ¬ (C381.det = 0 ∧ ∀ i, C381.adjugate i i ≠ 0) := by
  intro h
  have := certificate381
  rw [h.1] at this
  norm_num at this
def C382 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate382 : C382.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction382 : ¬ (C382.det = 0 ∧ ∀ i, C382.adjugate i i ≠ 0) := by
  intro h
  have := certificate382
  rw [h.1] at this
  norm_num at this
def C383 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate383 : C383.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction383 : ¬ (C383.det = 0 ∧ ∀ i, C383.adjugate i i ≠ 0) := by
  intro h
  have := certificate383
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0011
