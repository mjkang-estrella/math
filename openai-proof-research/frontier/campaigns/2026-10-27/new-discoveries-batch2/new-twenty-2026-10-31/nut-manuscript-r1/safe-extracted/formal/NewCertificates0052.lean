import VerifiedDet
namespace Nut8.NewCertificates0052
def C1664 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1664 : C1664.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1664 : ¬ (C1664.det = 0 ∧ ∀ i, C1664.adjugate i i ≠ 0) := by
  intro h
  have := certificate1664
  rw [h.1] at this
  norm_num at this
def C1665 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1665 : C1665.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1665 : ¬ (C1665.det = 0 ∧ ∀ i, C1665.adjugate i i ≠ 0) := by
  intro h
  have := certificate1665
  rw [h.1] at this
  norm_num at this
def C1666 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1666 : C1666.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1666 : ¬ (C1666.det = 0 ∧ ∀ i, C1666.adjugate i i ≠ 0) := by
  intro h
  have := certificate1666
  rw [h.1] at this
  norm_num at this
def C1667 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1667 : C1667.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1667 : ¬ (C1667.det = 0 ∧ ∀ i, C1667.adjugate i i ≠ 0) := by
  intro h
  have := certificate1667
  rw [h.1] at this
  norm_num at this
def C1668 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1668 : C1668.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1668 : ¬ (C1668.det = 0 ∧ ∀ i, C1668.adjugate i i ≠ 0) := by
  intro h
  have := certificate1668
  rw [h.1] at this
  norm_num at this
def C1669 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1669 : C1669.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1669 : ¬ (C1669.det = 0 ∧ ∀ i, C1669.adjugate i i ≠ 0) := by
  intro h
  have := certificate1669
  rw [h.1] at this
  norm_num at this
def C1670 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1670 : C1670.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1670 : ¬ (C1670.det = 0 ∧ ∀ i, C1670.adjugate i i ≠ 0) := by
  intro h
  have := certificate1670
  rw [h.1] at this
  norm_num at this
def C1671 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1671 : C1671.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1671 : ¬ (C1671.det = 0 ∧ ∀ i, C1671.adjugate i i ≠ 0) := by
  intro h
  have := certificate1671
  rw [h.1] at this
  norm_num at this
def C1672 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1672 : C1672.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1672 : ¬ (C1672.det = 0 ∧ ∀ i, C1672.adjugate i i ≠ 0) := by
  intro h
  have := certificate1672
  rw [h.1] at this
  norm_num at this
def C1673 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1673 : C1673.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1673 : ¬ (C1673.det = 0 ∧ ∀ i, C1673.adjugate i i ≠ 0) := by
  intro h
  have := certificate1673
  rw [h.1] at this
  norm_num at this
def C1674 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1674 : C1674.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1674 : ¬ (C1674.det = 0 ∧ ∀ i, C1674.adjugate i i ≠ 0) := by
  intro h
  have := certificate1674
  rw [h.1] at this
  norm_num at this
def C1675 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1675 : C1675.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1675 : ¬ (C1675.det = 0 ∧ ∀ i, C1675.adjugate i i ≠ 0) := by
  intro h
  have := certificate1675
  rw [h.1] at this
  norm_num at this
def C1676 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1676 : C1676.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1676 : ¬ (C1676.det = 0 ∧ ∀ i, C1676.adjugate i i ≠ 0) := by
  intro h
  have := certificate1676
  rw [h.1] at this
  norm_num at this
def C1677 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1677 : C1677.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1677 : ¬ (C1677.det = 0 ∧ ∀ i, C1677.adjugate i i ≠ 0) := by
  intro h
  have := certificate1677
  rw [h.1] at this
  norm_num at this
def C1678 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1678 : C1678.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1678 : ¬ (C1678.det = 0 ∧ ∀ i, C1678.adjugate i i ≠ 0) := by
  intro h
  have := certificate1678
  rw [h.1] at this
  norm_num at this
def C1679 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1679 : C1679.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1679 : ¬ (C1679.det = 0 ∧ ∀ i, C1679.adjugate i i ≠ 0) := by
  intro h
  have := certificate1679
  rw [h.1] at this
  norm_num at this
def C1680 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1680 : C1680.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1680 : ¬ (C1680.det = 0 ∧ ∀ i, C1680.adjugate i i ≠ 0) := by
  intro h
  have := certificate1680
  rw [h.1] at this
  norm_num at this
def C1681 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1681 : C1681.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1681 : ¬ (C1681.det = 0 ∧ ∀ i, C1681.adjugate i i ≠ 0) := by
  intro h
  have := certificate1681
  rw [h.1] at this
  norm_num at this
def C1682 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1682 : C1682.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1682 : ¬ (C1682.det = 0 ∧ ∀ i, C1682.adjugate i i ≠ 0) := by
  intro h
  have := certificate1682
  rw [h.1] at this
  norm_num at this
def C1683 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1683 : C1683.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1683 : ¬ (C1683.det = 0 ∧ ∀ i, C1683.adjugate i i ≠ 0) := by
  intro h
  have := certificate1683
  rw [h.1] at this
  norm_num at this
def C1684 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1684 : C1684.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1684 : ¬ (C1684.det = 0 ∧ ∀ i, C1684.adjugate i i ≠ 0) := by
  intro h
  have := certificate1684
  rw [h.1] at this
  norm_num at this
def C1685 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1685 : C1685.det = (92 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1685 : ¬ (C1685.det = 0 ∧ ∀ i, C1685.adjugate i i ≠ 0) := by
  intro h
  have := certificate1685
  rw [h.1] at this
  norm_num at this
def C1686 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1686 : C1686.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1686 : ¬ (C1686.det = 0 ∧ ∀ i, C1686.adjugate i i ≠ 0) := by
  intro h
  have := certificate1686
  rw [h.1] at this
  norm_num at this
def C1687 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1687 : C1687.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1687 : ¬ (C1687.det = 0 ∧ ∀ i, C1687.adjugate i i ≠ 0) := by
  intro h
  have := certificate1687
  rw [h.1] at this
  norm_num at this
def C1688 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1688 : C1688.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1688 : ¬ (C1688.det = 0 ∧ ∀ i, C1688.adjugate i i ≠ 0) := by
  intro h
  have := certificate1688
  rw [h.1] at this
  norm_num at this
def C1689 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1689 : C1689.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1689 : ¬ (C1689.det = 0 ∧ ∀ i, C1689.adjugate i i ≠ 0) := by
  intro h
  have := certificate1689
  rw [h.1] at this
  norm_num at this
def C1690 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1690 : C1690.det = (92 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1690 : ¬ (C1690.det = 0 ∧ ∀ i, C1690.adjugate i i ≠ 0) := by
  intro h
  have := certificate1690
  rw [h.1] at this
  norm_num at this
def C1691 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1691 : C1691.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1691 : ¬ (C1691.det = 0 ∧ ∀ i, C1691.adjugate i i ≠ 0) := by
  intro h
  have := certificate1691
  rw [h.1] at this
  norm_num at this
def C1692 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1692 : C1692.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1692 : ¬ (C1692.det = 0 ∧ ∀ i, C1692.adjugate i i ≠ 0) := by
  intro h
  have := certificate1692
  rw [h.1] at this
  norm_num at this
def C1693 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1693 : C1693.det = (140 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1693 : ¬ (C1693.det = 0 ∧ ∀ i, C1693.adjugate i i ≠ 0) := by
  intro h
  have := certificate1693
  rw [h.1] at this
  norm_num at this
def C1694 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1694 : C1694.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1694 : ¬ (C1694.det = 0 ∧ ∀ i, C1694.adjugate i i ≠ 0) := by
  intro h
  have := certificate1694
  rw [h.1] at this
  norm_num at this
def C1695 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1695 : C1695.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1695 : ¬ (C1695.det = 0 ∧ ∀ i, C1695.adjugate i i ≠ 0) := by
  intro h
  have := certificate1695
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0052
