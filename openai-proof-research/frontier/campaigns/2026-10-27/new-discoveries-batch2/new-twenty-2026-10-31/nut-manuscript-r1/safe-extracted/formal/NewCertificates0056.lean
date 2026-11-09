import VerifiedDet
namespace Nut8.NewCertificates0056
def C1792 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1792 : C1792.det = (255 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1792 : ¬ (C1792.det = 0 ∧ ∀ i, C1792.adjugate i i ≠ 0) := by
  intro h
  have := certificate1792
  rw [h.1] at this
  norm_num at this
def C1793 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1793 : C1793.det = (255 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1793 : ¬ (C1793.det = 0 ∧ ∀ i, C1793.adjugate i i ≠ 0) := by
  intro h
  have := certificate1793
  rw [h.1] at this
  norm_num at this
def C1794 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1794 : C1794.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1794 : ¬ (C1794.det = 0 ∧ ∀ i, C1794.adjugate i i ≠ 0) := by
  intro h
  have := certificate1794
  rw [h.1] at this
  norm_num at this
def C1795 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1795 : C1795.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1795 : ¬ (C1795.det = 0 ∧ ∀ i, C1795.adjugate i i ≠ 0) := by
  intro h
  have := certificate1795
  rw [h.1] at this
  norm_num at this
def C1796 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1796 : C1796.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1796 : ¬ (C1796.det = 0 ∧ ∀ i, C1796.adjugate i i ≠ 0) := by
  intro h
  have := certificate1796
  rw [h.1] at this
  norm_num at this
def C1797 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1797 : C1797.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1797 : ¬ (C1797.det = 0 ∧ ∀ i, C1797.adjugate i i ≠ 0) := by
  intro h
  have := certificate1797
  rw [h.1] at this
  norm_num at this
def C1798 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1798 : C1798.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1798 : ¬ (C1798.det = 0 ∧ ∀ i, C1798.adjugate i i ≠ 0) := by
  intro h
  have := certificate1798
  rw [h.1] at this
  norm_num at this
def C1799 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1799 : C1799.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1799 : ¬ (C1799.det = 0 ∧ ∀ i, C1799.adjugate i i ≠ 0) := by
  intro h
  have := certificate1799
  rw [h.1] at this
  norm_num at this
def C1800 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1800 : C1800.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1800 : ¬ (C1800.det = 0 ∧ ∀ i, C1800.adjugate i i ≠ 0) := by
  intro h
  have := certificate1800
  rw [h.1] at this
  norm_num at this
def C1801 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1801 : C1801.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1801 : ¬ (C1801.det = 0 ∧ ∀ i, C1801.adjugate i i ≠ 0) := by
  intro h
  have := certificate1801
  rw [h.1] at this
  norm_num at this
def C1802 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1802 : C1802.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1802 : ¬ (C1802.det = 0 ∧ ∀ i, C1802.adjugate i i ≠ 0) := by
  intro h
  have := certificate1802
  rw [h.1] at this
  norm_num at this
def C1803 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1803 : C1803.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1803 : ¬ (C1803.det = 0 ∧ ∀ i, C1803.adjugate i i ≠ 0) := by
  intro h
  have := certificate1803
  rw [h.1] at this
  norm_num at this
def C1804 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1804 : C1804.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1804 : ¬ (C1804.det = 0 ∧ ∀ i, C1804.adjugate i i ≠ 0) := by
  intro h
  have := certificate1804
  rw [h.1] at this
  norm_num at this
def C1805 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1805 : C1805.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1805 : ¬ (C1805.det = 0 ∧ ∀ i, C1805.adjugate i i ≠ 0) := by
  intro h
  have := certificate1805
  rw [h.1] at this
  norm_num at this
def C1806 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1806 : C1806.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1806 : ¬ (C1806.det = 0 ∧ ∀ i, C1806.adjugate i i ≠ 0) := by
  intro h
  have := certificate1806
  rw [h.1] at this
  norm_num at this
def C1807 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1807 : C1807.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1807 : ¬ (C1807.det = 0 ∧ ∀ i, C1807.adjugate i i ≠ 0) := by
  intro h
  have := certificate1807
  rw [h.1] at this
  norm_num at this
def C1808 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1808 : C1808.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1808 : ¬ (C1808.det = 0 ∧ ∀ i, C1808.adjugate i i ≠ 0) := by
  intro h
  have := certificate1808
  rw [h.1] at this
  norm_num at this
def C1809 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1809 : C1809.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1809 : ¬ (C1809.det = 0 ∧ ∀ i, C1809.adjugate i i ≠ 0) := by
  intro h
  have := certificate1809
  rw [h.1] at this
  norm_num at this
def C1810 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1810 : C1810.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1810 : ¬ (C1810.det = 0 ∧ ∀ i, C1810.adjugate i i ≠ 0) := by
  intro h
  have := certificate1810
  rw [h.1] at this
  norm_num at this
def C1811 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1811 : C1811.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1811 : ¬ (C1811.det = 0 ∧ ∀ i, C1811.adjugate i i ≠ 0) := by
  intro h
  have := certificate1811
  rw [h.1] at this
  norm_num at this
def C1812 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1812 : C1812.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1812 : ¬ (C1812.det = 0 ∧ ∀ i, C1812.adjugate i i ≠ 0) := by
  intro h
  have := certificate1812
  rw [h.1] at this
  norm_num at this
def C1813 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1813 : C1813.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1813 : ¬ (C1813.det = 0 ∧ ∀ i, C1813.adjugate i i ≠ 0) := by
  intro h
  have := certificate1813
  rw [h.1] at this
  norm_num at this
def C1814 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1814 : C1814.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1814 : ¬ (C1814.det = 0 ∧ ∀ i, C1814.adjugate i i ≠ 0) := by
  intro h
  have := certificate1814
  rw [h.1] at this
  norm_num at this
def C1815 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1815 : C1815.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1815 : ¬ (C1815.det = 0 ∧ ∀ i, C1815.adjugate i i ≠ 0) := by
  intro h
  have := certificate1815
  rw [h.1] at this
  norm_num at this
def C1816 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1816 : C1816.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1816 : ¬ (C1816.det = 0 ∧ ∀ i, C1816.adjugate i i ≠ 0) := by
  intro h
  have := certificate1816
  rw [h.1] at this
  norm_num at this
def C1817 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1817 : C1817.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1817 : ¬ (C1817.det = 0 ∧ ∀ i, C1817.adjugate i i ≠ 0) := by
  intro h
  have := certificate1817
  rw [h.1] at this
  norm_num at this
def C1818 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1818 : C1818.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1818 : ¬ (C1818.det = 0 ∧ ∀ i, C1818.adjugate i i ≠ 0) := by
  intro h
  have := certificate1818
  rw [h.1] at this
  norm_num at this
def C1819 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1819 : C1819.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1819 : ¬ (C1819.det = 0 ∧ ∀ i, C1819.adjugate i i ≠ 0) := by
  intro h
  have := certificate1819
  rw [h.1] at this
  norm_num at this
def C1820 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1820 : C1820.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1820 : ¬ (C1820.det = 0 ∧ ∀ i, C1820.adjugate i i ≠ 0) := by
  intro h
  have := certificate1820
  rw [h.1] at this
  norm_num at this
def C1821 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1821 : C1821.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1821 : ¬ (C1821.det = 0 ∧ ∀ i, C1821.adjugate i i ≠ 0) := by
  intro h
  have := certificate1821
  rw [h.1] at this
  norm_num at this
def C1822 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1822 : C1822.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1822 : ¬ (C1822.det = 0 ∧ ∀ i, C1822.adjugate i i ≠ 0) := by
  intro h
  have := certificate1822
  rw [h.1] at this
  norm_num at this
def C1823 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1823 : C1823.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1823 : ¬ (C1823.det = 0 ∧ ∀ i, C1823.adjugate i i ≠ 0) := by
  intro h
  have := certificate1823
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0056
