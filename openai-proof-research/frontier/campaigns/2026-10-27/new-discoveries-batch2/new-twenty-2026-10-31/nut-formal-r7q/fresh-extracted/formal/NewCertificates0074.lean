import VerifiedDet
namespace Nut8.NewCertificates0074
def C2368 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2368 : C2368.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2368 : ¬ (C2368.det = 0 ∧ ∀ i, C2368.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate2368
def C2369 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2369 : C2369.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2369 : ¬ (C2369.det = 0 ∧ ∀ i, C2369.adjugate i i ≠ 0) := by
  intro h
  have := certificate2369
  rw [h.1] at this
  norm_num at this
def C2370 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2370 : C2370.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2370 : ¬ (C2370.det = 0 ∧ ∀ i, C2370.adjugate i i ≠ 0) := by
  intro h
  have := certificate2370
  rw [h.1] at this
  norm_num at this
def C2371 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2371 : C2371.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2371 : ¬ (C2371.det = 0 ∧ ∀ i, C2371.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate2371
def C2372 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2372 : C2372.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2372 : ¬ (C2372.det = 0 ∧ ∀ i, C2372.adjugate i i ≠ 0) := by
  intro h
  have := certificate2372
  rw [h.1] at this
  norm_num at this
def C2373 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2373 : C2373.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2373 : ¬ (C2373.det = 0 ∧ ∀ i, C2373.adjugate i i ≠ 0) := by
  intro h
  have := certificate2373
  rw [h.1] at this
  norm_num at this
def C2374 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2374 : C2374.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2374 : ¬ (C2374.det = 0 ∧ ∀ i, C2374.adjugate i i ≠ 0) := by
  intro h
  have := certificate2374
  rw [h.1] at this
  norm_num at this
def C2375 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2375 : C2375.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2375 : ¬ (C2375.det = 0 ∧ ∀ i, C2375.adjugate i i ≠ 0) := by
  intro h
  have := certificate2375
  rw [h.1] at this
  norm_num at this
def C2376 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2376 : C2376.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2376 : ¬ (C2376.det = 0 ∧ ∀ i, C2376.adjugate i i ≠ 0) := by
  intro h
  have := certificate2376
  rw [h.1] at this
  norm_num at this
def C2377 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2377 : C2377.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2377 : ¬ (C2377.det = 0 ∧ ∀ i, C2377.adjugate i i ≠ 0) := by
  intro h
  have := certificate2377
  rw [h.1] at this
  norm_num at this
def C2378 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2378 : C2378.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2378 : ¬ (C2378.det = 0 ∧ ∀ i, C2378.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2378
def C2379 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2379 : C2379.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2379 : ¬ (C2379.det = 0 ∧ ∀ i, C2379.adjugate i i ≠ 0) := by
  intro h
  have := certificate2379
  rw [h.1] at this
  norm_num at this
def C2380 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2380 : C2380.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2380 : ¬ (C2380.det = 0 ∧ ∀ i, C2380.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2380
def C2381 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2381 : C2381.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2381 : ¬ (C2381.det = 0 ∧ ∀ i, C2381.adjugate i i ≠ 0) := by
  intro h
  have := certificate2381
  rw [h.1] at this
  norm_num at this
def C2382 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2382 : C2382.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2382 : ¬ (C2382.det = 0 ∧ ∀ i, C2382.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2382
def C2383 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2383 : C2383.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2383 : ¬ (C2383.det = 0 ∧ ∀ i, C2383.adjugate i i ≠ 0) := by
  intro h
  have := certificate2383
  rw [h.1] at this
  norm_num at this
def C2384 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2384 : C2384.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2384 : ¬ (C2384.det = 0 ∧ ∀ i, C2384.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2384
def C2385 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2385 : C2385.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2385 : ¬ (C2385.det = 0 ∧ ∀ i, C2385.adjugate i i ≠ 0) := by
  intro h
  have := certificate2385
  rw [h.1] at this
  norm_num at this
def C2386 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2386 : C2386.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2386 : ¬ (C2386.det = 0 ∧ ∀ i, C2386.adjugate i i ≠ 0) := by
  intro h
  have := certificate2386
  rw [h.1] at this
  norm_num at this
def C2387 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2387 : C2387.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2387 : ¬ (C2387.det = 0 ∧ ∀ i, C2387.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2387
def C2388 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2388 : C2388.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2388 : ¬ (C2388.det = 0 ∧ ∀ i, C2388.adjugate i i ≠ 0) := by
  intro h
  have := certificate2388
  rw [h.1] at this
  norm_num at this
def C2389 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2389 : C2389.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2389 : ¬ (C2389.det = 0 ∧ ∀ i, C2389.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2389
def C2390 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2390 : C2390.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2390 : ¬ (C2390.det = 0 ∧ ∀ i, C2390.adjugate i i ≠ 0) := by
  intro h
  have := certificate2390
  rw [h.1] at this
  norm_num at this
def C2391 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2391 : C2391.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2391 : ¬ (C2391.det = 0 ∧ ∀ i, C2391.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2391
def C2392 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2392 : C2392.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2392 : ¬ (C2392.det = 0 ∧ ∀ i, C2392.adjugate i i ≠ 0) := by
  intro h
  have := certificate2392
  rw [h.1] at this
  norm_num at this
def C2393 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2393 : C2393.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2393 : ¬ (C2393.det = 0 ∧ ∀ i, C2393.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2393
def C2394 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2394 : C2394.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2394 : ¬ (C2394.det = 0 ∧ ∀ i, C2394.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2394
def C2395 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2395 : C2395.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2395 : ¬ (C2395.det = 0 ∧ ∀ i, C2395.adjugate i i ≠ 0) := by
  intro h
  have := certificate2395
  rw [h.1] at this
  norm_num at this
def C2396 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2396 : C2396.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2396 : ¬ (C2396.det = 0 ∧ ∀ i, C2396.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2396
def C2397 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2397 : C2397.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2397 : ¬ (C2397.det = 0 ∧ ∀ i, C2397.adjugate i i ≠ 0) := by
  intro h
  have := certificate2397
  rw [h.1] at this
  norm_num at this
def C2398 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2398 : C2398.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2398 : ¬ (C2398.det = 0 ∧ ∀ i, C2398.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2398
def C2399 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2399 : C2399.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2399 : ¬ (C2399.det = 0 ∧ ∀ i, C2399.adjugate i i ≠ 0) := by
  intro h
  have := certificate2399
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0074
