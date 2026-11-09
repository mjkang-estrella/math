import VerifiedDet
namespace Nut8.NewCertificates0199
def C6368 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6368 : C6368.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6368 : ¬ (C6368.det = 0 ∧ ∀ i, C6368.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6368
def C6369 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6369 : C6369.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6369 : ¬ (C6369.det = 0 ∧ ∀ i, C6369.adjugate i i ≠ 0) := by
  intro h
  have := certificate6369
  rw [h.1] at this
  norm_num at this
def C6370 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6370 : C6370.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6370 : ¬ (C6370.det = 0 ∧ ∀ i, C6370.adjugate i i ≠ 0) := by
  intro h
  have := certificate6370
  rw [h.1] at this
  norm_num at this
def C6371 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6371 : C6371.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6371 : ¬ (C6371.det = 0 ∧ ∀ i, C6371.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6371
def C6372 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6372 : C6372.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6372 : ¬ (C6372.det = 0 ∧ ∀ i, C6372.adjugate i i ≠ 0) := by
  intro h
  have := certificate6372
  rw [h.1] at this
  norm_num at this
def C6373 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6373 : C6373.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6373 : ¬ (C6373.det = 0 ∧ ∀ i, C6373.adjugate i i ≠ 0) := by
  intro h
  have := certificate6373
  rw [h.1] at this
  norm_num at this
def C6374 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6374 : C6374.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6374 : ¬ (C6374.det = 0 ∧ ∀ i, C6374.adjugate i i ≠ 0) := by
  intro h
  have := certificate6374
  rw [h.1] at this
  norm_num at this
def C6375 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6375 : C6375.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6375 : ¬ (C6375.det = 0 ∧ ∀ i, C6375.adjugate i i ≠ 0) := by
  intro h
  have := certificate6375
  rw [h.1] at this
  norm_num at this
def C6376 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6376 : C6376.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6376 : ¬ (C6376.det = 0 ∧ ∀ i, C6376.adjugate i i ≠ 0) := by
  intro h
  have := certificate6376
  rw [h.1] at this
  norm_num at this
def C6377 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6377 : C6377.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6377 : ¬ (C6377.det = 0 ∧ ∀ i, C6377.adjugate i i ≠ 0) := by
  intro h
  have := certificate6377
  rw [h.1] at this
  norm_num at this
def C6378 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6378 : C6378.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6378 : ¬ (C6378.det = 0 ∧ ∀ i, C6378.adjugate i i ≠ 0) := by
  intro h
  have := certificate6378
  rw [h.1] at this
  norm_num at this
def C6379 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6379 : C6379.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6379 : ¬ (C6379.det = 0 ∧ ∀ i, C6379.adjugate i i ≠ 0) := by
  intro h
  have := certificate6379
  rw [h.1] at this
  norm_num at this
def C6380 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6380 : C6380.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6380 : ¬ (C6380.det = 0 ∧ ∀ i, C6380.adjugate i i ≠ 0) := by
  intro h
  have := certificate6380
  rw [h.1] at this
  norm_num at this
def C6381 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6381 : C6381.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6381 : ¬ (C6381.det = 0 ∧ ∀ i, C6381.adjugate i i ≠ 0) := by
  intro h
  have := certificate6381
  rw [h.1] at this
  norm_num at this
def C6382 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6382 : C6382.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6382 : ¬ (C6382.det = 0 ∧ ∀ i, C6382.adjugate i i ≠ 0) := by
  intro h
  have := certificate6382
  rw [h.1] at this
  norm_num at this
def C6383 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6383 : C6383.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6383 : ¬ (C6383.det = 0 ∧ ∀ i, C6383.adjugate i i ≠ 0) := by
  intro h
  have := certificate6383
  rw [h.1] at this
  norm_num at this
def C6384 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6384 : C6384.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6384 : ¬ (C6384.det = 0 ∧ ∀ i, C6384.adjugate i i ≠ 0) := by
  intro h
  have := certificate6384
  rw [h.1] at this
  norm_num at this
def C6385 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6385 : C6385.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6385 : ¬ (C6385.det = 0 ∧ ∀ i, C6385.adjugate i i ≠ 0) := by
  intro h
  have := certificate6385
  rw [h.1] at this
  norm_num at this
def C6386 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6386 : C6386.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6386 : ¬ (C6386.det = 0 ∧ ∀ i, C6386.adjugate i i ≠ 0) := by
  intro h
  have := certificate6386
  rw [h.1] at this
  norm_num at this
def C6387 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6387 : C6387.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6387 : ¬ (C6387.det = 0 ∧ ∀ i, C6387.adjugate i i ≠ 0) := by
  intro h
  have := certificate6387
  rw [h.1] at this
  norm_num at this
def C6388 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6388 : C6388.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6388 : ¬ (C6388.det = 0 ∧ ∀ i, C6388.adjugate i i ≠ 0) := by
  intro h
  have := certificate6388
  rw [h.1] at this
  norm_num at this
def C6389 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6389 : C6389.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6389 : ¬ (C6389.det = 0 ∧ ∀ i, C6389.adjugate i i ≠ 0) := by
  intro h
  have := certificate6389
  rw [h.1] at this
  norm_num at this
def C6390 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6390 : C6390.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6390 : ¬ (C6390.det = 0 ∧ ∀ i, C6390.adjugate i i ≠ 0) := by
  intro h
  have := certificate6390
  rw [h.1] at this
  norm_num at this
def C6391 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6391 : C6391.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6391 : ¬ (C6391.det = 0 ∧ ∀ i, C6391.adjugate i i ≠ 0) := by
  intro h
  have := certificate6391
  rw [h.1] at this
  norm_num at this
def C6392 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6392 : C6392.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6392 : ¬ (C6392.det = 0 ∧ ∀ i, C6392.adjugate i i ≠ 0) := by
  intro h
  have := certificate6392
  rw [h.1] at this
  norm_num at this
def C6393 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6393 : C6393.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6393 : ¬ (C6393.det = 0 ∧ ∀ i, C6393.adjugate i i ≠ 0) := by
  intro h
  have := certificate6393
  rw [h.1] at this
  norm_num at this
def C6394 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6394 : C6394.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6394 : ¬ (C6394.det = 0 ∧ ∀ i, C6394.adjugate i i ≠ 0) := by
  intro h
  have := certificate6394
  rw [h.1] at this
  norm_num at this
def C6395 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6395 : C6395.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6395 : ¬ (C6395.det = 0 ∧ ∀ i, C6395.adjugate i i ≠ 0) := by
  intro h
  have := certificate6395
  rw [h.1] at this
  norm_num at this
def C6396 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6396 : C6396.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6396 : ¬ (C6396.det = 0 ∧ ∀ i, C6396.adjugate i i ≠ 0) := by
  intro h
  have := certificate6396
  rw [h.1] at this
  norm_num at this
def C6397 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6397 : C6397.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6397 : ¬ (C6397.det = 0 ∧ ∀ i, C6397.adjugate i i ≠ 0) := by
  intro h
  have := certificate6397
  rw [h.1] at this
  norm_num at this
def C6398 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6398 : C6398.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6398 : ¬ (C6398.det = 0 ∧ ∀ i, C6398.adjugate i i ≠ 0) := by
  intro h
  have := certificate6398
  rw [h.1] at this
  norm_num at this
def C6399 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6399 : C6399.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6399 : ¬ (C6399.det = 0 ∧ ∀ i, C6399.adjugate i i ≠ 0) := by
  intro h
  have := certificate6399
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0199
