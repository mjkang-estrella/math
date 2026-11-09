import VerifiedDet
namespace Nut8.NewCertificates0073
def C2336 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2336 : C2336.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2336 : ¬ (C2336.det = 0 ∧ ∀ i, C2336.adjugate i i ≠ 0) := by
  intro h
  have := certificate2336
  rw [h.1] at this
  norm_num at this
def C2337 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2337 : C2337.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2337 : ¬ (C2337.det = 0 ∧ ∀ i, C2337.adjugate i i ≠ 0) := by
  intro h
  have := certificate2337
  rw [h.1] at this
  norm_num at this
def C2338 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2338 : C2338.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2338 : ¬ (C2338.det = 0 ∧ ∀ i, C2338.adjugate i i ≠ 0) := by
  intro h
  have := certificate2338
  rw [h.1] at this
  norm_num at this
def C2339 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2339 : C2339.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2339 : ¬ (C2339.det = 0 ∧ ∀ i, C2339.adjugate i i ≠ 0) := by
  intro h
  have := certificate2339
  rw [h.1] at this
  norm_num at this
def C2340 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2340 : C2340.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2340 : ¬ (C2340.det = 0 ∧ ∀ i, C2340.adjugate i i ≠ 0) := by
  intro h
  have := certificate2340
  rw [h.1] at this
  norm_num at this
def C2341 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2341 : C2341.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2341 : ¬ (C2341.det = 0 ∧ ∀ i, C2341.adjugate i i ≠ 0) := by
  intro h
  have := certificate2341
  rw [h.1] at this
  norm_num at this
def C2342 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2342 : C2342.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2342 : ¬ (C2342.det = 0 ∧ ∀ i, C2342.adjugate i i ≠ 0) := by
  intro h
  have := certificate2342
  rw [h.1] at this
  norm_num at this
def C2343 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2343 : C2343.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2343 : ¬ (C2343.det = 0 ∧ ∀ i, C2343.adjugate i i ≠ 0) := by
  intro h
  have := certificate2343
  rw [h.1] at this
  norm_num at this
def C2344 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2344 : C2344.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2344 : ¬ (C2344.det = 0 ∧ ∀ i, C2344.adjugate i i ≠ 0) := by
  intro h
  have := certificate2344
  rw [h.1] at this
  norm_num at this
def C2345 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2345 : C2345.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2345 : ¬ (C2345.det = 0 ∧ ∀ i, C2345.adjugate i i ≠ 0) := by
  intro h
  have := certificate2345
  rw [h.1] at this
  norm_num at this
def C2346 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2346 : C2346.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2346 : ¬ (C2346.det = 0 ∧ ∀ i, C2346.adjugate i i ≠ 0) := by
  intro h
  have := certificate2346
  rw [h.1] at this
  norm_num at this
def C2347 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2347 : C2347.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2347 : ¬ (C2347.det = 0 ∧ ∀ i, C2347.adjugate i i ≠ 0) := by
  intro h
  have := certificate2347
  rw [h.1] at this
  norm_num at this
def C2348 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2348 : C2348.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2348 : ¬ (C2348.det = 0 ∧ ∀ i, C2348.adjugate i i ≠ 0) := by
  intro h
  have := certificate2348
  rw [h.1] at this
  norm_num at this
def C2349 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2349 : C2349.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2349 : ¬ (C2349.det = 0 ∧ ∀ i, C2349.adjugate i i ≠ 0) := by
  intro h
  have := certificate2349
  rw [h.1] at this
  norm_num at this
def C2350 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2350 : C2350.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2350 : ¬ (C2350.det = 0 ∧ ∀ i, C2350.adjugate i i ≠ 0) := by
  intro h
  have := certificate2350
  rw [h.1] at this
  norm_num at this
def C2351 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2351 : C2351.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2351 : ¬ (C2351.det = 0 ∧ ∀ i, C2351.adjugate i i ≠ 0) := by
  intro h
  have := certificate2351
  rw [h.1] at this
  norm_num at this
def C2352 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2352 : C2352.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2352 : ¬ (C2352.det = 0 ∧ ∀ i, C2352.adjugate i i ≠ 0) := by
  intro h
  have := certificate2352
  rw [h.1] at this
  norm_num at this
def C2353 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2353 : C2353.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2353 : ¬ (C2353.det = 0 ∧ ∀ i, C2353.adjugate i i ≠ 0) := by
  intro h
  have := certificate2353
  rw [h.1] at this
  norm_num at this
def C2354 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2354 : C2354.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2354 : ¬ (C2354.det = 0 ∧ ∀ i, C2354.adjugate i i ≠ 0) := by
  intro h
  have := certificate2354
  rw [h.1] at this
  norm_num at this
def C2355 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2355 : C2355.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2355 : ¬ (C2355.det = 0 ∧ ∀ i, C2355.adjugate i i ≠ 0) := by
  intro h
  have := certificate2355
  rw [h.1] at this
  norm_num at this
def C2356 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2356 : C2356.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2356 : ¬ (C2356.det = 0 ∧ ∀ i, C2356.adjugate i i ≠ 0) := by
  intro h
  have := certificate2356
  rw [h.1] at this
  norm_num at this
def C2357 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2357 : C2357.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2357 : ¬ (C2357.det = 0 ∧ ∀ i, C2357.adjugate i i ≠ 0) := by
  intro h
  have := certificate2357
  rw [h.1] at this
  norm_num at this
def C2358 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2358 : C2358.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2358 : ¬ (C2358.det = 0 ∧ ∀ i, C2358.adjugate i i ≠ 0) := by
  intro h
  have := certificate2358
  rw [h.1] at this
  norm_num at this
def C2359 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2359 : C2359.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2359 : ¬ (C2359.det = 0 ∧ ∀ i, C2359.adjugate i i ≠ 0) := by
  intro h
  have := certificate2359
  rw [h.1] at this
  norm_num at this
def C2360 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2360 : C2360.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2360 : ¬ (C2360.det = 0 ∧ ∀ i, C2360.adjugate i i ≠ 0) := by
  intro h
  have := certificate2360
  rw [h.1] at this
  norm_num at this
def C2361 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2361 : C2361.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2361 : ¬ (C2361.det = 0 ∧ ∀ i, C2361.adjugate i i ≠ 0) := by
  intro h
  have := certificate2361
  rw [h.1] at this
  norm_num at this
def C2362 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2362 : C2362.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2362 : ¬ (C2362.det = 0 ∧ ∀ i, C2362.adjugate i i ≠ 0) := by
  intro h
  have := certificate2362
  rw [h.1] at this
  norm_num at this
def C2363 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2363 : C2363.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2363 : ¬ (C2363.det = 0 ∧ ∀ i, C2363.adjugate i i ≠ 0) := by
  intro h
  have := certificate2363
  rw [h.1] at this
  norm_num at this
def C2364 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2364 : C2364.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2364 : ¬ (C2364.det = 0 ∧ ∀ i, C2364.adjugate i i ≠ 0) := by
  intro h
  have := certificate2364
  rw [h.1] at this
  norm_num at this
def C2365 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2365 : C2365.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2365 : ¬ (C2365.det = 0 ∧ ∀ i, C2365.adjugate i i ≠ 0) := by
  intro h
  have := certificate2365
  rw [h.1] at this
  norm_num at this
def C2366 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2366 : C2366.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2366 : ¬ (C2366.det = 0 ∧ ∀ i, C2366.adjugate i i ≠ 0) := by
  intro h
  have := certificate2366
  rw [h.1] at this
  norm_num at this
def C2367 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2367 : C2367.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2367 : ¬ (C2367.det = 0 ∧ ∀ i, C2367.adjugate i i ≠ 0) := by
  intro h
  have := certificate2367
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0073
