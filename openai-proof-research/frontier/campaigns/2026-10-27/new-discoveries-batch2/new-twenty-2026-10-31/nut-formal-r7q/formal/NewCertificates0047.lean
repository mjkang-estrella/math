import VerifiedDet
namespace Nut8.NewCertificates0047
def C1504 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1504 : C1504.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1504 : ¬ (C1504.det = 0 ∧ ∀ i, C1504.adjugate i i ≠ 0) := by
  intro h
  have := certificate1504
  rw [h.1] at this
  norm_num at this
def C1505 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1505 : C1505.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1505 : ¬ (C1505.det = 0 ∧ ∀ i, C1505.adjugate i i ≠ 0) := by
  intro h
  have := certificate1505
  rw [h.1] at this
  norm_num at this
def C1506 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1506 : C1506.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1506 : ¬ (C1506.det = 0 ∧ ∀ i, C1506.adjugate i i ≠ 0) := by
  intro h
  have := certificate1506
  rw [h.1] at this
  norm_num at this
def C1507 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1507 : C1507.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1507 : ¬ (C1507.det = 0 ∧ ∀ i, C1507.adjugate i i ≠ 0) := by
  intro h
  have := certificate1507
  rw [h.1] at this
  norm_num at this
def C1508 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1508 : C1508.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1508 : ¬ (C1508.det = 0 ∧ ∀ i, C1508.adjugate i i ≠ 0) := by
  intro h
  have := certificate1508
  rw [h.1] at this
  norm_num at this
def C1509 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1509 : C1509.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1509 : ¬ (C1509.det = 0 ∧ ∀ i, C1509.adjugate i i ≠ 0) := by
  intro h
  have := certificate1509
  rw [h.1] at this
  norm_num at this
def C1510 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1510 : C1510.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1510 : ¬ (C1510.det = 0 ∧ ∀ i, C1510.adjugate i i ≠ 0) := by
  intro h
  have := certificate1510
  rw [h.1] at this
  norm_num at this
def C1511 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1511 : C1511.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1511 : ¬ (C1511.det = 0 ∧ ∀ i, C1511.adjugate i i ≠ 0) := by
  intro h
  have := certificate1511
  rw [h.1] at this
  norm_num at this
def C1512 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1512 : C1512.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1512 : ¬ (C1512.det = 0 ∧ ∀ i, C1512.adjugate i i ≠ 0) := by
  intro h
  have := certificate1512
  rw [h.1] at this
  norm_num at this
def C1513 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1513 : C1513.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1513 : ¬ (C1513.det = 0 ∧ ∀ i, C1513.adjugate i i ≠ 0) := by
  intro h
  have := certificate1513
  rw [h.1] at this
  norm_num at this
def C1514 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1514 : C1514.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1514 : ¬ (C1514.det = 0 ∧ ∀ i, C1514.adjugate i i ≠ 0) := by
  intro h
  have := certificate1514
  rw [h.1] at this
  norm_num at this
def C1515 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1515 : C1515.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1515 : ¬ (C1515.det = 0 ∧ ∀ i, C1515.adjugate i i ≠ 0) := by
  intro h
  have := certificate1515
  rw [h.1] at this
  norm_num at this
def C1516 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1516 : C1516.det = (-57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1516 : ¬ (C1516.det = 0 ∧ ∀ i, C1516.adjugate i i ≠ 0) := by
  intro h
  have := certificate1516
  rw [h.1] at this
  norm_num at this
def C1517 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1517 : C1517.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1517 : ¬ (C1517.det = 0 ∧ ∀ i, C1517.adjugate i i ≠ 0) := by
  intro h
  have := certificate1517
  rw [h.1] at this
  norm_num at this
def C1518 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1518 : C1518.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1518 : ¬ (C1518.det = 0 ∧ ∀ i, C1518.adjugate i i ≠ 0) := by
  intro h
  have := certificate1518
  rw [h.1] at this
  norm_num at this
def C1519 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1519 : C1519.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1519 : ¬ (C1519.det = 0 ∧ ∀ i, C1519.adjugate i i ≠ 0) := by
  intro h
  have := certificate1519
  rw [h.1] at this
  norm_num at this
def C1520 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1520 : C1520.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1520 : ¬ (C1520.det = 0 ∧ ∀ i, C1520.adjugate i i ≠ 0) := by
  intro h
  have := certificate1520
  rw [h.1] at this
  norm_num at this
def C1521 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1521 : C1521.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1521 : ¬ (C1521.det = 0 ∧ ∀ i, C1521.adjugate i i ≠ 0) := by
  intro h
  have := certificate1521
  rw [h.1] at this
  norm_num at this
def C1522 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1522 : C1522.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1522 : ¬ (C1522.det = 0 ∧ ∀ i, C1522.adjugate i i ≠ 0) := by
  intro h
  have := certificate1522
  rw [h.1] at this
  norm_num at this
def C1523 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1523 : C1523.det = (-57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1523 : ¬ (C1523.det = 0 ∧ ∀ i, C1523.adjugate i i ≠ 0) := by
  intro h
  have := certificate1523
  rw [h.1] at this
  norm_num at this
def C1524 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1524 : C1524.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1524 : ¬ (C1524.det = 0 ∧ ∀ i, C1524.adjugate i i ≠ 0) := by
  intro h
  have := certificate1524
  rw [h.1] at this
  norm_num at this
def C1525 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1525 : C1525.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1525 : ¬ (C1525.det = 0 ∧ ∀ i, C1525.adjugate i i ≠ 0) := by
  intro h
  have := certificate1525
  rw [h.1] at this
  norm_num at this
def C1526 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1526 : C1526.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1526 : ¬ (C1526.det = 0 ∧ ∀ i, C1526.adjugate i i ≠ 0) := by
  intro h
  have := certificate1526
  rw [h.1] at this
  norm_num at this
def C1527 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1527 : C1527.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1527 : ¬ (C1527.det = 0 ∧ ∀ i, C1527.adjugate i i ≠ 0) := by
  intro h
  have := certificate1527
  rw [h.1] at this
  norm_num at this
def C1528 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1528 : C1528.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1528 : ¬ (C1528.det = 0 ∧ ∀ i, C1528.adjugate i i ≠ 0) := by
  intro h
  have := certificate1528
  rw [h.1] at this
  norm_num at this
def C1529 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1529 : C1529.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1529 : ¬ (C1529.det = 0 ∧ ∀ i, C1529.adjugate i i ≠ 0) := by
  intro h
  have := certificate1529
  rw [h.1] at this
  norm_num at this
def C1530 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1530 : C1530.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1530 : ¬ (C1530.det = 0 ∧ ∀ i, C1530.adjugate i i ≠ 0) := by
  intro h
  have := certificate1530
  rw [h.1] at this
  norm_num at this
def C1531 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1531 : C1531.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1531 : ¬ (C1531.det = 0 ∧ ∀ i, C1531.adjugate i i ≠ 0) := by
  intro h
  have := certificate1531
  rw [h.1] at this
  norm_num at this
def C1532 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1532 : C1532.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1532 : ¬ (C1532.det = 0 ∧ ∀ i, C1532.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1532
def C1533 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1533 : C1533.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1533 : ¬ (C1533.det = 0 ∧ ∀ i, C1533.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1533
def C1534 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1534 : C1534.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1534 : ¬ (C1534.det = 0 ∧ ∀ i, C1534.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1534
def C1535 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1535 : C1535.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1535 : ¬ (C1535.det = 0 ∧ ∀ i, C1535.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1535
end Nut8.NewCertificates0047
