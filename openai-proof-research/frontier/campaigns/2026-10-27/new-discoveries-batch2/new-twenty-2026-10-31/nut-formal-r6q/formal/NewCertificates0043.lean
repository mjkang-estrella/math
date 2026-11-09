import VerifiedDet
namespace Nut8.NewCertificates0043
def C1376 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1376 : C1376.det = (-78 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1376 : ¬ (C1376.det = 0 ∧ ∀ i, C1376.adjugate i i ≠ 0) := by
  intro h
  have := certificate1376
  rw [h.1] at this
  norm_num at this
def C1377 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1377 : C1377.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1377 : ¬ (C1377.det = 0 ∧ ∀ i, C1377.adjugate i i ≠ 0) := by
  intro h
  have := certificate1377
  rw [h.1] at this
  norm_num at this
def C1378 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1378 : C1378.det = (82 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1378 : ¬ (C1378.det = 0 ∧ ∀ i, C1378.adjugate i i ≠ 0) := by
  intro h
  have := certificate1378
  rw [h.1] at this
  norm_num at this
def C1379 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1379 : C1379.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1379 : ¬ (C1379.det = 0 ∧ ∀ i, C1379.adjugate i i ≠ 0) := by
  intro h
  have := certificate1379
  rw [h.1] at this
  norm_num at this
def C1380 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1380 : C1380.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1380 : ¬ (C1380.det = 0 ∧ ∀ i, C1380.adjugate i i ≠ 0) := by
  intro h
  have := certificate1380
  rw [h.1] at this
  norm_num at this
def C1381 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1381 : C1381.det = (82 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1381 : ¬ (C1381.det = 0 ∧ ∀ i, C1381.adjugate i i ≠ 0) := by
  intro h
  have := certificate1381
  rw [h.1] at this
  norm_num at this
def C1382 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1382 : C1382.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1382 : ¬ (C1382.det = 0 ∧ ∀ i, C1382.adjugate i i ≠ 0) := by
  intro h
  have := certificate1382
  rw [h.1] at this
  norm_num at this
def C1383 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1383 : C1383.det = (-78 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1383 : ¬ (C1383.det = 0 ∧ ∀ i, C1383.adjugate i i ≠ 0) := by
  intro h
  have := certificate1383
  rw [h.1] at this
  norm_num at this
def C1384 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1384 : C1384.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1384 : ¬ (C1384.det = 0 ∧ ∀ i, C1384.adjugate i i ≠ 0) := by
  intro h
  have := certificate1384
  rw [h.1] at this
  norm_num at this
def C1385 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1385 : C1385.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1385 : ¬ (C1385.det = 0 ∧ ∀ i, C1385.adjugate i i ≠ 0) := by
  intro h
  have := certificate1385
  rw [h.1] at this
  norm_num at this
def C1386 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1386 : C1386.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1386 : ¬ (C1386.det = 0 ∧ ∀ i, C1386.adjugate i i ≠ 0) := by
  intro h
  have := certificate1386
  rw [h.1] at this
  norm_num at this
def C1387 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1387 : C1387.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1387 : ¬ (C1387.det = 0 ∧ ∀ i, C1387.adjugate i i ≠ 0) := by
  intro h
  have := certificate1387
  rw [h.1] at this
  norm_num at this
def C1388 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1388 : C1388.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1388 : ¬ (C1388.det = 0 ∧ ∀ i, C1388.adjugate i i ≠ 0) := by
  intro h
  have := certificate1388
  rw [h.1] at this
  norm_num at this
def C1389 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1389 : C1389.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1389 : ¬ (C1389.det = 0 ∧ ∀ i, C1389.adjugate i i ≠ 0) := by
  intro h
  have := certificate1389
  rw [h.1] at this
  norm_num at this
def C1390 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1390 : C1390.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1390 : ¬ (C1390.det = 0 ∧ ∀ i, C1390.adjugate i i ≠ 0) := by
  intro h
  have := certificate1390
  rw [h.1] at this
  norm_num at this
def C1391 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1391 : C1391.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1391 : ¬ (C1391.det = 0 ∧ ∀ i, C1391.adjugate i i ≠ 0) := by
  intro h
  have := certificate1391
  rw [h.1] at this
  norm_num at this
def C1392 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1392 : C1392.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1392 : ¬ (C1392.det = 0 ∧ ∀ i, C1392.adjugate i i ≠ 0) := by
  intro h
  have := certificate1392
  rw [h.1] at this
  norm_num at this
def C1393 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1393 : C1393.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1393 : ¬ (C1393.det = 0 ∧ ∀ i, C1393.adjugate i i ≠ 0) := by
  intro h
  have := certificate1393
  rw [h.1] at this
  norm_num at this
def C1394 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1394 : C1394.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1394 : ¬ (C1394.det = 0 ∧ ∀ i, C1394.adjugate i i ≠ 0) := by
  intro h
  have := certificate1394
  rw [h.1] at this
  norm_num at this
def C1395 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1395 : C1395.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1395 : ¬ (C1395.det = 0 ∧ ∀ i, C1395.adjugate i i ≠ 0) := by
  intro h
  have := certificate1395
  rw [h.1] at this
  norm_num at this
def C1396 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1396 : C1396.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1396 : ¬ (C1396.det = 0 ∧ ∀ i, C1396.adjugate i i ≠ 0) := by
  intro h
  have := certificate1396
  rw [h.1] at this
  norm_num at this
def C1397 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1397 : C1397.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1397 : ¬ (C1397.det = 0 ∧ ∀ i, C1397.adjugate i i ≠ 0) := by
  intro h
  have := certificate1397
  rw [h.1] at this
  norm_num at this
def C1398 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1398 : C1398.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1398 : ¬ (C1398.det = 0 ∧ ∀ i, C1398.adjugate i i ≠ 0) := by
  intro h
  have := certificate1398
  rw [h.1] at this
  norm_num at this
def C1399 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1399 : C1399.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1399 : ¬ (C1399.det = 0 ∧ ∀ i, C1399.adjugate i i ≠ 0) := by
  intro h
  have := certificate1399
  rw [h.1] at this
  norm_num at this
def C1400 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1400 : C1400.det = (-78 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1400 : ¬ (C1400.det = 0 ∧ ∀ i, C1400.adjugate i i ≠ 0) := by
  intro h
  have := certificate1400
  rw [h.1] at this
  norm_num at this
def C1401 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1401 : C1401.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1401 : ¬ (C1401.det = 0 ∧ ∀ i, C1401.adjugate i i ≠ 0) := by
  intro h
  have := certificate1401
  rw [h.1] at this
  norm_num at this
def C1402 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1402 : C1402.det = (106 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1402 : ¬ (C1402.det = 0 ∧ ∀ i, C1402.adjugate i i ≠ 0) := by
  intro h
  have := certificate1402
  rw [h.1] at this
  norm_num at this
def C1403 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1403 : C1403.det = (46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1403 : ¬ (C1403.det = 0 ∧ ∀ i, C1403.adjugate i i ≠ 0) := by
  intro h
  have := certificate1403
  rw [h.1] at this
  norm_num at this
def C1404 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1404 : C1404.det = (46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1404 : ¬ (C1404.det = 0 ∧ ∀ i, C1404.adjugate i i ≠ 0) := by
  intro h
  have := certificate1404
  rw [h.1] at this
  norm_num at this
def C1405 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1405 : C1405.det = (106 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1405 : ¬ (C1405.det = 0 ∧ ∀ i, C1405.adjugate i i ≠ 0) := by
  intro h
  have := certificate1405
  rw [h.1] at this
  norm_num at this
def C1406 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1406 : C1406.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1406 : ¬ (C1406.det = 0 ∧ ∀ i, C1406.adjugate i i ≠ 0) := by
  intro h
  have := certificate1406
  rw [h.1] at this
  norm_num at this
def C1407 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1407 : C1407.det = (-78 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1407 : ¬ (C1407.det = 0 ∧ ∀ i, C1407.adjugate i i ≠ 0) := by
  intro h
  have := certificate1407
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0043
