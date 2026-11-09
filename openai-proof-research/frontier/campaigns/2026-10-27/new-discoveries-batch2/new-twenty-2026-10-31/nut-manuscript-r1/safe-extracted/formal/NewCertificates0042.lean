import VerifiedDet
namespace Nut8.NewCertificates0042
def C1344 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1344 : C1344.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1344 : ¬ (C1344.det = 0 ∧ ∀ i, C1344.adjugate i i ≠ 0) := by
  intro h
  have := certificate1344
  rw [h.1] at this
  norm_num at this
def C1345 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1345 : C1345.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1345 : ¬ (C1345.det = 0 ∧ ∀ i, C1345.adjugate i i ≠ 0) := by
  intro h
  have := certificate1345
  rw [h.1] at this
  norm_num at this
def C1346 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1346 : C1346.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1346 : ¬ (C1346.det = 0 ∧ ∀ i, C1346.adjugate i i ≠ 0) := by
  intro h
  have := certificate1346
  rw [h.1] at this
  norm_num at this
def C1347 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1347 : C1347.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1347 : ¬ (C1347.det = 0 ∧ ∀ i, C1347.adjugate i i ≠ 0) := by
  intro h
  have := certificate1347
  rw [h.1] at this
  norm_num at this
def C1348 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1348 : C1348.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1348 : ¬ (C1348.det = 0 ∧ ∀ i, C1348.adjugate i i ≠ 0) := by
  intro h
  have := certificate1348
  rw [h.1] at this
  norm_num at this
def C1349 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1349 : C1349.det = (-57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1349 : ¬ (C1349.det = 0 ∧ ∀ i, C1349.adjugate i i ≠ 0) := by
  intro h
  have := certificate1349
  rw [h.1] at this
  norm_num at this
def C1350 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1350 : C1350.det = (-61 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1350 : ¬ (C1350.det = 0 ∧ ∀ i, C1350.adjugate i i ≠ 0) := by
  intro h
  have := certificate1350
  rw [h.1] at this
  norm_num at this
def C1351 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1351 : C1351.det = (55 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1351 : ¬ (C1351.det = 0 ∧ ∀ i, C1351.adjugate i i ≠ 0) := by
  intro h
  have := certificate1351
  rw [h.1] at this
  norm_num at this
def C1352 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1352 : C1352.det = (-97 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1352 : ¬ (C1352.det = 0 ∧ ∀ i, C1352.adjugate i i ≠ 0) := by
  intro h
  have := certificate1352
  rw [h.1] at this
  norm_num at this
def C1353 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1353 : C1353.det = (43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1353 : ¬ (C1353.det = 0 ∧ ∀ i, C1353.adjugate i i ≠ 0) := by
  intro h
  have := certificate1353
  rw [h.1] at this
  norm_num at this
def C1354 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1354 : C1354.det = (111 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1354 : ¬ (C1354.det = 0 ∧ ∀ i, C1354.adjugate i i ≠ 0) := by
  intro h
  have := certificate1354
  rw [h.1] at this
  norm_num at this
def C1355 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1355 : C1355.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1355 : ¬ (C1355.det = 0 ∧ ∀ i, C1355.adjugate i i ≠ 0) := by
  intro h
  have := certificate1355
  rw [h.1] at this
  norm_num at this
def C1356 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1356 : C1356.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1356 : ¬ (C1356.det = 0 ∧ ∀ i, C1356.adjugate i i ≠ 0) := by
  intro h
  have := certificate1356
  rw [h.1] at this
  norm_num at this
def C1357 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1357 : C1357.det = (111 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1357 : ¬ (C1357.det = 0 ∧ ∀ i, C1357.adjugate i i ≠ 0) := by
  intro h
  have := certificate1357
  rw [h.1] at this
  norm_num at this
def C1358 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1358 : C1358.det = (43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1358 : ¬ (C1358.det = 0 ∧ ∀ i, C1358.adjugate i i ≠ 0) := by
  intro h
  have := certificate1358
  rw [h.1] at this
  norm_num at this
def C1359 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1359 : C1359.det = (-97 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1359 : ¬ (C1359.det = 0 ∧ ∀ i, C1359.adjugate i i ≠ 0) := by
  intro h
  have := certificate1359
  rw [h.1] at this
  norm_num at this
def C1360 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1360 : C1360.det = (55 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1360 : ¬ (C1360.det = 0 ∧ ∀ i, C1360.adjugate i i ≠ 0) := by
  intro h
  have := certificate1360
  rw [h.1] at this
  norm_num at this
def C1361 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1361 : C1361.det = (-61 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1361 : ¬ (C1361.det = 0 ∧ ∀ i, C1361.adjugate i i ≠ 0) := by
  intro h
  have := certificate1361
  rw [h.1] at this
  norm_num at this
def C1362 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1362 : C1362.det = (-57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1362 : ¬ (C1362.det = 0 ∧ ∀ i, C1362.adjugate i i ≠ 0) := by
  intro h
  have := certificate1362
  rw [h.1] at this
  norm_num at this
def C1363 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1363 : C1363.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1363 : ¬ (C1363.det = 0 ∧ ∀ i, C1363.adjugate i i ≠ 0) := by
  intro h
  have := certificate1363
  rw [h.1] at this
  norm_num at this
def C1364 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1364 : C1364.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1364 : ¬ (C1364.det = 0 ∧ ∀ i, C1364.adjugate i i ≠ 0) := by
  intro h
  have := certificate1364
  rw [h.1] at this
  norm_num at this
def C1365 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1365 : C1365.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1365 : ¬ (C1365.det = 0 ∧ ∀ i, C1365.adjugate i i ≠ 0) := by
  intro h
  have := certificate1365
  rw [h.1] at this
  norm_num at this
def C1366 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1366 : C1366.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1366 : ¬ (C1366.det = 0 ∧ ∀ i, C1366.adjugate i i ≠ 0) := by
  intro h
  have := certificate1366
  rw [h.1] at this
  norm_num at this
def C1367 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1367 : C1367.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1367 : ¬ (C1367.det = 0 ∧ ∀ i, C1367.adjugate i i ≠ 0) := by
  intro h
  have := certificate1367
  rw [h.1] at this
  norm_num at this
def C1368 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1368 : C1368.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1368 : ¬ (C1368.det = 0 ∧ ∀ i, C1368.adjugate i i ≠ 0) := by
  intro h
  have := certificate1368
  rw [h.1] at this
  norm_num at this
def C1369 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1369 : C1369.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1369 : ¬ (C1369.det = 0 ∧ ∀ i, C1369.adjugate i i ≠ 0) := by
  intro h
  have := certificate1369
  rw [h.1] at this
  norm_num at this
def C1370 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1370 : C1370.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1370 : ¬ (C1370.det = 0 ∧ ∀ i, C1370.adjugate i i ≠ 0) := by
  intro h
  have := certificate1370
  rw [h.1] at this
  norm_num at this
def C1371 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1371 : C1371.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1371 : ¬ (C1371.det = 0 ∧ ∀ i, C1371.adjugate i i ≠ 0) := by
  intro h
  have := certificate1371
  rw [h.1] at this
  norm_num at this
def C1372 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1372 : C1372.det = (-42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1372 : ¬ (C1372.det = 0 ∧ ∀ i, C1372.adjugate i i ≠ 0) := by
  intro h
  have := certificate1372
  rw [h.1] at this
  norm_num at this
def C1373 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1373 : C1373.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1373 : ¬ (C1373.det = 0 ∧ ∀ i, C1373.adjugate i i ≠ 0) := by
  intro h
  have := certificate1373
  rw [h.1] at this
  norm_num at this
def C1374 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1374 : C1374.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1374 : ¬ (C1374.det = 0 ∧ ∀ i, C1374.adjugate i i ≠ 0) := by
  intro h
  have := certificate1374
  rw [h.1] at this
  norm_num at this
def C1375 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1375 : C1375.det = (-42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1375 : ¬ (C1375.det = 0 ∧ ∀ i, C1375.adjugate i i ≠ 0) := by
  intro h
  have := certificate1375
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0042
