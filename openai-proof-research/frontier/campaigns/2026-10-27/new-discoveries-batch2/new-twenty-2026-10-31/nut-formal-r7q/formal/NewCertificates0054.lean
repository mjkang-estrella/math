import VerifiedDet
namespace Nut8.NewCertificates0054
def C1728 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1728 : C1728.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1728 : ¬ (C1728.det = 0 ∧ ∀ i, C1728.adjugate i i ≠ 0) := by
  intro h
  have := certificate1728
  rw [h.1] at this
  norm_num at this
def C1729 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1729 : C1729.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1729 : ¬ (C1729.det = 0 ∧ ∀ i, C1729.adjugate i i ≠ 0) := by
  intro h
  have := certificate1729
  rw [h.1] at this
  norm_num at this
def C1730 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1730 : C1730.det = (92 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1730 : ¬ (C1730.det = 0 ∧ ∀ i, C1730.adjugate i i ≠ 0) := by
  intro h
  have := certificate1730
  rw [h.1] at this
  norm_num at this
def C1731 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1731 : C1731.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1731 : ¬ (C1731.det = 0 ∧ ∀ i, C1731.adjugate i i ≠ 0) := by
  intro h
  have := certificate1731
  rw [h.1] at this
  norm_num at this
def C1732 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1732 : C1732.det = (-120 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1732 : ¬ (C1732.det = 0 ∧ ∀ i, C1732.adjugate i i ≠ 0) := by
  intro h
  have := certificate1732
  rw [h.1] at this
  norm_num at this
def C1733 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1733 : C1733.det = (152 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1733 : ¬ (C1733.det = 0 ∧ ∀ i, C1733.adjugate i i ≠ 0) := by
  intro h
  have := certificate1733
  rw [h.1] at this
  norm_num at this
def C1734 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1734 : C1734.det = (152 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1734 : ¬ (C1734.det = 0 ∧ ∀ i, C1734.adjugate i i ≠ 0) := by
  intro h
  have := certificate1734
  rw [h.1] at this
  norm_num at this
def C1735 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1735 : C1735.det = (-120 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1735 : ¬ (C1735.det = 0 ∧ ∀ i, C1735.adjugate i i ≠ 0) := by
  intro h
  have := certificate1735
  rw [h.1] at this
  norm_num at this
def C1736 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1736 : C1736.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1736 : ¬ (C1736.det = 0 ∧ ∀ i, C1736.adjugate i i ≠ 0) := by
  intro h
  have := certificate1736
  rw [h.1] at this
  norm_num at this
def C1737 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1737 : C1737.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1737 : ¬ (C1737.det = 0 ∧ ∀ i, C1737.adjugate i i ≠ 0) := by
  intro h
  have := certificate1737
  rw [h.1] at this
  norm_num at this
def C1738 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1738 : C1738.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1738 : ¬ (C1738.det = 0 ∧ ∀ i, C1738.adjugate i i ≠ 0) := by
  intro h
  have := certificate1738
  rw [h.1] at this
  norm_num at this
def C1739 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1739 : C1739.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1739 : ¬ (C1739.det = 0 ∧ ∀ i, C1739.adjugate i i ≠ 0) := by
  intro h
  have := certificate1739
  rw [h.1] at this
  norm_num at this
def C1740 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1740 : C1740.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1740 : ¬ (C1740.det = 0 ∧ ∀ i, C1740.adjugate i i ≠ 0) := by
  intro h
  have := certificate1740
  rw [h.1] at this
  norm_num at this
def C1741 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1741 : C1741.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1741 : ¬ (C1741.det = 0 ∧ ∀ i, C1741.adjugate i i ≠ 0) := by
  intro h
  have := certificate1741
  rw [h.1] at this
  norm_num at this
def C1742 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1742 : C1742.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1742 : ¬ (C1742.det = 0 ∧ ∀ i, C1742.adjugate i i ≠ 0) := by
  intro h
  have := certificate1742
  rw [h.1] at this
  norm_num at this
def C1743 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1743 : C1743.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1743 : ¬ (C1743.det = 0 ∧ ∀ i, C1743.adjugate i i ≠ 0) := by
  intro h
  have := certificate1743
  rw [h.1] at this
  norm_num at this
def C1744 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1744 : C1744.det = (-156 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1744 : ¬ (C1744.det = 0 ∧ ∀ i, C1744.adjugate i i ≠ 0) := by
  intro h
  have := certificate1744
  rw [h.1] at this
  norm_num at this
def C1745 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1745 : C1745.det = (164 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1745 : ¬ (C1745.det = 0 ∧ ∀ i, C1745.adjugate i i ≠ 0) := by
  intro h
  have := certificate1745
  rw [h.1] at this
  norm_num at this
def C1746 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1746 : C1746.det = (164 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1746 : ¬ (C1746.det = 0 ∧ ∀ i, C1746.adjugate i i ≠ 0) := by
  intro h
  have := certificate1746
  rw [h.1] at this
  norm_num at this
def C1747 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1747 : C1747.det = (-156 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1747 : ¬ (C1747.det = 0 ∧ ∀ i, C1747.adjugate i i ≠ 0) := by
  intro h
  have := certificate1747
  rw [h.1] at this
  norm_num at this
def C1748 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1748 : C1748.det = (-255 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1748 : ¬ (C1748.det = 0 ∧ ∀ i, C1748.adjugate i i ≠ 0) := by
  intro h
  have := certificate1748
  rw [h.1] at this
  norm_num at this
def C1749 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1749 : C1749.det = (257 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1749 : ¬ (C1749.det = 0 ∧ ∀ i, C1749.adjugate i i ≠ 0) := by
  intro h
  have := certificate1749
  rw [h.1] at this
  norm_num at this
def C1750 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1750 : C1750.det = (257 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1750 : ¬ (C1750.det = 0 ∧ ∀ i, C1750.adjugate i i ≠ 0) := by
  intro h
  have := certificate1750
  rw [h.1] at this
  norm_num at this
def C1751 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1751 : C1751.det = (-255 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1751 : ¬ (C1751.det = 0 ∧ ∀ i, C1751.adjugate i i ≠ 0) := by
  intro h
  have := certificate1751
  rw [h.1] at this
  norm_num at this
def C1752 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1752 : C1752.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1752 : ¬ (C1752.det = 0 ∧ ∀ i, C1752.adjugate i i ≠ 0) := by
  intro h
  have := certificate1752
  rw [h.1] at this
  norm_num at this
def C1753 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1753 : C1753.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1753 : ¬ (C1753.det = 0 ∧ ∀ i, C1753.adjugate i i ≠ 0) := by
  intro h
  have := certificate1753
  rw [h.1] at this
  norm_num at this
def C1754 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1754 : C1754.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1754 : ¬ (C1754.det = 0 ∧ ∀ i, C1754.adjugate i i ≠ 0) := by
  intro h
  have := certificate1754
  rw [h.1] at this
  norm_num at this
def C1755 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1755 : C1755.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1755 : ¬ (C1755.det = 0 ∧ ∀ i, C1755.adjugate i i ≠ 0) := by
  intro h
  have := certificate1755
  rw [h.1] at this
  norm_num at this
def C1756 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1756 : C1756.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1756 : ¬ (C1756.det = 0 ∧ ∀ i, C1756.adjugate i i ≠ 0) := by
  intro h
  have := certificate1756
  rw [h.1] at this
  norm_num at this
def C1757 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1757 : C1757.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1757 : ¬ (C1757.det = 0 ∧ ∀ i, C1757.adjugate i i ≠ 0) := by
  intro h
  have := certificate1757
  rw [h.1] at this
  norm_num at this
def C1758 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1758 : C1758.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1758 : ¬ (C1758.det = 0 ∧ ∀ i, C1758.adjugate i i ≠ 0) := by
  intro h
  have := certificate1758
  rw [h.1] at this
  norm_num at this
def C1759 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1759 : C1759.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1759 : ¬ (C1759.det = 0 ∧ ∀ i, C1759.adjugate i i ≠ 0) := by
  intro h
  have := certificate1759
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0054
