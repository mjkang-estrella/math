import VerifiedDet
namespace Nut8.NewCertificates0045
def C1440 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1440 : C1440.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1440 : ¬ (C1440.det = 0 ∧ ∀ i, C1440.adjugate i i ≠ 0) := by
  intro h
  have := certificate1440
  rw [h.1] at this
  norm_num at this
def C1441 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1441 : C1441.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1441 : ¬ (C1441.det = 0 ∧ ∀ i, C1441.adjugate i i ≠ 0) := by
  intro h
  have := certificate1441
  rw [h.1] at this
  norm_num at this
def C1442 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1442 : C1442.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1442 : ¬ (C1442.det = 0 ∧ ∀ i, C1442.adjugate i i ≠ 0) := by
  intro h
  have := certificate1442
  rw [h.1] at this
  norm_num at this
def C1443 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1443 : C1443.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1443 : ¬ (C1443.det = 0 ∧ ∀ i, C1443.adjugate i i ≠ 0) := by
  intro h
  have := certificate1443
  rw [h.1] at this
  norm_num at this
def C1444 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1444 : C1444.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1444 : ¬ (C1444.det = 0 ∧ ∀ i, C1444.adjugate i i ≠ 0) := by
  intro h
  have := certificate1444
  rw [h.1] at this
  norm_num at this
def C1445 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1445 : C1445.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1445 : ¬ (C1445.det = 0 ∧ ∀ i, C1445.adjugate i i ≠ 0) := by
  intro h
  have := certificate1445
  rw [h.1] at this
  norm_num at this
def C1446 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1446 : C1446.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1446 : ¬ (C1446.det = 0 ∧ ∀ i, C1446.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate1446
def C1447 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1447 : C1447.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1447 : ¬ (C1447.det = 0 ∧ ∀ i, C1447.adjugate i i ≠ 0) := by
  intro h
  have := certificate1447
  rw [h.1] at this
  norm_num at this
def C1448 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1448 : C1448.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1448 : ¬ (C1448.det = 0 ∧ ∀ i, C1448.adjugate i i ≠ 0) := by
  intro h
  have := certificate1448
  rw [h.1] at this
  norm_num at this
def C1449 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1449 : C1449.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1449 : ¬ (C1449.det = 0 ∧ ∀ i, C1449.adjugate i i ≠ 0) := by
  intro h
  have := certificate1449
  rw [h.1] at this
  norm_num at this
def C1450 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1450 : C1450.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1450 : ¬ (C1450.det = 0 ∧ ∀ i, C1450.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate1450
def C1451 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1451 : C1451.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1451 : ¬ (C1451.det = 0 ∧ ∀ i, C1451.adjugate i i ≠ 0) := by
  intro h
  have := certificate1451
  rw [h.1] at this
  norm_num at this
def C1452 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1452 : C1452.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1452 : ¬ (C1452.det = 0 ∧ ∀ i, C1452.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate1452
def C1453 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1453 : C1453.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1453 : ¬ (C1453.det = 0 ∧ ∀ i, C1453.adjugate i i ≠ 0) := by
  intro h
  have := certificate1453
  rw [h.1] at this
  norm_num at this
def C1454 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1454 : C1454.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1454 : ¬ (C1454.det = 0 ∧ ∀ i, C1454.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate1454
def C1455 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1455 : C1455.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1455 : ¬ (C1455.det = 0 ∧ ∀ i, C1455.adjugate i i ≠ 0) := by
  intro h
  have := certificate1455
  rw [h.1] at this
  norm_num at this
def C1456 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1456 : C1456.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1456 : ¬ (C1456.det = 0 ∧ ∀ i, C1456.adjugate i i ≠ 0) := by
  intro h
  have := certificate1456
  rw [h.1] at this
  norm_num at this
def C1457 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1457 : C1457.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1457 : ¬ (C1457.det = 0 ∧ ∀ i, C1457.adjugate i i ≠ 0) := by
  intro h
  have := certificate1457
  rw [h.1] at this
  norm_num at this
def C1458 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1458 : C1458.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1458 : ¬ (C1458.det = 0 ∧ ∀ i, C1458.adjugate i i ≠ 0) := by
  intro h
  have := certificate1458
  rw [h.1] at this
  norm_num at this
def C1459 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1459 : C1459.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1459 : ¬ (C1459.det = 0 ∧ ∀ i, C1459.adjugate i i ≠ 0) := by
  intro h
  have := certificate1459
  rw [h.1] at this
  norm_num at this
def C1460 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1460 : C1460.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1460 : ¬ (C1460.det = 0 ∧ ∀ i, C1460.adjugate i i ≠ 0) := by
  intro h
  have := certificate1460
  rw [h.1] at this
  norm_num at this
def C1461 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1461 : C1461.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1461 : ¬ (C1461.det = 0 ∧ ∀ i, C1461.adjugate i i ≠ 0) := by
  intro h
  have := certificate1461
  rw [h.1] at this
  norm_num at this
def C1462 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1462 : C1462.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1462 : ¬ (C1462.det = 0 ∧ ∀ i, C1462.adjugate i i ≠ 0) := by
  intro h
  have := certificate1462
  rw [h.1] at this
  norm_num at this
def C1463 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1463 : C1463.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1463 : ¬ (C1463.det = 0 ∧ ∀ i, C1463.adjugate i i ≠ 0) := by
  intro h
  have := certificate1463
  rw [h.1] at this
  norm_num at this
def C1464 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1464 : C1464.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1464 : ¬ (C1464.det = 0 ∧ ∀ i, C1464.adjugate i i ≠ 0) := by
  intro h
  have := certificate1464
  rw [h.1] at this
  norm_num at this
def C1465 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1465 : C1465.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1465 : ¬ (C1465.det = 0 ∧ ∀ i, C1465.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate1465
def C1466 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1466 : C1466.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1466 : ¬ (C1466.det = 0 ∧ ∀ i, C1466.adjugate i i ≠ 0) := by
  intro h
  have := certificate1466
  rw [h.1] at this
  norm_num at this
def C1467 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1467 : C1467.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1467 : ¬ (C1467.det = 0 ∧ ∀ i, C1467.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate1467
def C1468 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1468 : C1468.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1468 : ¬ (C1468.det = 0 ∧ ∀ i, C1468.adjugate i i ≠ 0) := by
  intro h
  have := certificate1468
  rw [h.1] at this
  norm_num at this
def C1469 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1469 : C1469.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1469 : ¬ (C1469.det = 0 ∧ ∀ i, C1469.adjugate i i ≠ 0) := by
  intro h
  have := certificate1469
  rw [h.1] at this
  norm_num at this
def C1470 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1470 : C1470.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1470 : ¬ (C1470.det = 0 ∧ ∀ i, C1470.adjugate i i ≠ 0) := by
  intro h
  have := certificate1470
  rw [h.1] at this
  norm_num at this
def C1471 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1471 : C1471.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1471 : ¬ (C1471.det = 0 ∧ ∀ i, C1471.adjugate i i ≠ 0) := by
  intro h
  have := certificate1471
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0045
