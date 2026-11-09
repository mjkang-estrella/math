import VerifiedDet
namespace Nut8.NewCertificates0044
def C1408 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1408 : C1408.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1408 : ¬ (C1408.det = 0 ∧ ∀ i, C1408.adjugate i i ≠ 0) := by
  intro h
  have := certificate1408
  rw [h.1] at this
  norm_num at this
def C1409 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1409 : C1409.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1409 : ¬ (C1409.det = 0 ∧ ∀ i, C1409.adjugate i i ≠ 0) := by
  intro h
  have := certificate1409
  rw [h.1] at this
  norm_num at this
def C1410 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1410 : C1410.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1410 : ¬ (C1410.det = 0 ∧ ∀ i, C1410.adjugate i i ≠ 0) := by
  intro h
  have := certificate1410
  rw [h.1] at this
  norm_num at this
def C1411 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1411 : C1411.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1411 : ¬ (C1411.det = 0 ∧ ∀ i, C1411.adjugate i i ≠ 0) := by
  intro h
  have := certificate1411
  rw [h.1] at this
  norm_num at this
def C1412 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1412 : C1412.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1412 : ¬ (C1412.det = 0 ∧ ∀ i, C1412.adjugate i i ≠ 0) := by
  intro h
  have := certificate1412
  rw [h.1] at this
  norm_num at this
def C1413 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1413 : C1413.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1413 : ¬ (C1413.det = 0 ∧ ∀ i, C1413.adjugate i i ≠ 0) := by
  intro h
  have := certificate1413
  rw [h.1] at this
  norm_num at this
def C1414 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1414 : C1414.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1414 : ¬ (C1414.det = 0 ∧ ∀ i, C1414.adjugate i i ≠ 0) := by
  intro h
  have := certificate1414
  rw [h.1] at this
  norm_num at this
def C1415 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1415 : C1415.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1415 : ¬ (C1415.det = 0 ∧ ∀ i, C1415.adjugate i i ≠ 0) := by
  intro h
  have := certificate1415
  rw [h.1] at this
  norm_num at this
def C1416 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1416 : C1416.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1416 : ¬ (C1416.det = 0 ∧ ∀ i, C1416.adjugate i i ≠ 0) := by
  intro h
  have := certificate1416
  rw [h.1] at this
  norm_num at this
def C1417 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1417 : C1417.det = (104 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1417 : ¬ (C1417.det = 0 ∧ ∀ i, C1417.adjugate i i ≠ 0) := by
  intro h
  have := certificate1417
  rw [h.1] at this
  norm_num at this
def C1418 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1418 : C1418.det = (104 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1418 : ¬ (C1418.det = 0 ∧ ∀ i, C1418.adjugate i i ≠ 0) := by
  intro h
  have := certificate1418
  rw [h.1] at this
  norm_num at this
def C1419 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1419 : C1419.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1419 : ¬ (C1419.det = 0 ∧ ∀ i, C1419.adjugate i i ≠ 0) := by
  intro h
  have := certificate1419
  rw [h.1] at this
  norm_num at this
def C1420 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1420 : C1420.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1420 : ¬ (C1420.det = 0 ∧ ∀ i, C1420.adjugate i i ≠ 0) := by
  intro h
  have := certificate1420
  rw [h.1] at this
  norm_num at this
def C1421 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1421 : C1421.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1421 : ¬ (C1421.det = 0 ∧ ∀ i, C1421.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate1421
def C1422 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1422 : C1422.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1422 : ¬ (C1422.det = 0 ∧ ∀ i, C1422.adjugate i i ≠ 0) := by
  intro h
  have := certificate1422
  rw [h.1] at this
  norm_num at this
def C1423 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1423 : C1423.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1423 : ¬ (C1423.det = 0 ∧ ∀ i, C1423.adjugate i i ≠ 0) := by
  intro h
  have := certificate1423
  rw [h.1] at this
  norm_num at this
def C1424 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1424 : C1424.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1424 : ¬ (C1424.det = 0 ∧ ∀ i, C1424.adjugate i i ≠ 0) := by
  intro h
  have := certificate1424
  rw [h.1] at this
  norm_num at this
def C1425 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1425 : C1425.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1425 : ¬ (C1425.det = 0 ∧ ∀ i, C1425.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate1425
def C1426 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1426 : C1426.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1426 : ¬ (C1426.det = 0 ∧ ∀ i, C1426.adjugate i i ≠ 0) := by
  intro h
  have := certificate1426
  rw [h.1] at this
  norm_num at this
def C1427 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1427 : C1427.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1427 : ¬ (C1427.det = 0 ∧ ∀ i, C1427.adjugate i i ≠ 0) := by
  intro h
  have := certificate1427
  rw [h.1] at this
  norm_num at this
def C1428 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1428 : C1428.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1428 : ¬ (C1428.det = 0 ∧ ∀ i, C1428.adjugate i i ≠ 0) := by
  intro h
  have := certificate1428
  rw [h.1] at this
  norm_num at this
def C1429 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1429 : C1429.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1429 : ¬ (C1429.det = 0 ∧ ∀ i, C1429.adjugate i i ≠ 0) := by
  intro h
  have := certificate1429
  rw [h.1] at this
  norm_num at this
def C1430 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1430 : C1430.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1430 : ¬ (C1430.det = 0 ∧ ∀ i, C1430.adjugate i i ≠ 0) := by
  intro h
  have := certificate1430
  rw [h.1] at this
  norm_num at this
def C1431 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1431 : C1431.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1431 : ¬ (C1431.det = 0 ∧ ∀ i, C1431.adjugate i i ≠ 0) := by
  intro h
  have := certificate1431
  rw [h.1] at this
  norm_num at this
def C1432 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1432 : C1432.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1432 : ¬ (C1432.det = 0 ∧ ∀ i, C1432.adjugate i i ≠ 0) := by
  intro h
  have := certificate1432
  rw [h.1] at this
  norm_num at this
def C1433 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1433 : C1433.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1433 : ¬ (C1433.det = 0 ∧ ∀ i, C1433.adjugate i i ≠ 0) := by
  intro h
  have := certificate1433
  rw [h.1] at this
  norm_num at this
def C1434 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1434 : C1434.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1434 : ¬ (C1434.det = 0 ∧ ∀ i, C1434.adjugate i i ≠ 0) := by
  intro h
  have := certificate1434
  rw [h.1] at this
  norm_num at this
def C1435 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1435 : C1435.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1435 : ¬ (C1435.det = 0 ∧ ∀ i, C1435.adjugate i i ≠ 0) := by
  intro h
  have := certificate1435
  rw [h.1] at this
  norm_num at this
def C1436 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1436 : C1436.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1436 : ¬ (C1436.det = 0 ∧ ∀ i, C1436.adjugate i i ≠ 0) := by
  intro h
  have := certificate1436
  rw [h.1] at this
  norm_num at this
def C1437 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1437 : C1437.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1437 : ¬ (C1437.det = 0 ∧ ∀ i, C1437.adjugate i i ≠ 0) := by
  intro h
  have := certificate1437
  rw [h.1] at this
  norm_num at this
def C1438 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1438 : C1438.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1438 : ¬ (C1438.det = 0 ∧ ∀ i, C1438.adjugate i i ≠ 0) := by
  intro h
  have := certificate1438
  rw [h.1] at this
  norm_num at this
def C1439 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1439 : C1439.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1439 : ¬ (C1439.det = 0 ∧ ∀ i, C1439.adjugate i i ≠ 0) := by
  intro h
  have := certificate1439
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0044
