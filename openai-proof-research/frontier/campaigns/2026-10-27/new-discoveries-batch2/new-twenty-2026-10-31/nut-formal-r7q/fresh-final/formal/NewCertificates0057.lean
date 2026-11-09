import VerifiedDet
namespace Nut8.NewCertificates0057
def C1824 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1824 : C1824.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1824 : ¬ (C1824.det = 0 ∧ ∀ i, C1824.adjugate i i ≠ 0) := by
  intro h
  have := certificate1824
  rw [h.1] at this
  norm_num at this
def C1825 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1825 : C1825.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1825 : ¬ (C1825.det = 0 ∧ ∀ i, C1825.adjugate i i ≠ 0) := by
  intro h
  have := certificate1825
  rw [h.1] at this
  norm_num at this
def C1826 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate1826 : C1826.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1826 : ¬ (C1826.det = 0 ∧ ∀ i, C1826.adjugate i i ≠ 0) := by
  intro h
  have := certificate1826
  rw [h.1] at this
  norm_num at this
def C1827 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate1827 : C1827.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1827 : ¬ (C1827.det = 0 ∧ ∀ i, C1827.adjugate i i ≠ 0) := by
  intro h
  have := certificate1827
  rw [h.1] at this
  norm_num at this
def C1828 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate1828 : C1828.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1828 : ¬ (C1828.det = 0 ∧ ∀ i, C1828.adjugate i i ≠ 0) := by
  intro h
  have := certificate1828
  rw [h.1] at this
  norm_num at this
def C1829 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate1829 : C1829.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1829 : ¬ (C1829.det = 0 ∧ ∀ i, C1829.adjugate i i ≠ 0) := by
  intro h
  have := certificate1829
  rw [h.1] at this
  norm_num at this
def C1830 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate1830 : C1830.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1830 : ¬ (C1830.det = 0 ∧ ∀ i, C1830.adjugate i i ≠ 0) := by
  intro h
  have := certificate1830
  rw [h.1] at this
  norm_num at this
def C1831 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate1831 : C1831.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1831 : ¬ (C1831.det = 0 ∧ ∀ i, C1831.adjugate i i ≠ 0) := by
  intro h
  have := certificate1831
  rw [h.1] at this
  norm_num at this
def C1832 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate1832 : C1832.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1832 : ¬ (C1832.det = 0 ∧ ∀ i, C1832.adjugate i i ≠ 0) := by
  intro h
  have := certificate1832
  rw [h.1] at this
  norm_num at this
def C1833 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate1833 : C1833.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1833 : ¬ (C1833.det = 0 ∧ ∀ i, C1833.adjugate i i ≠ 0) := by
  intro h
  have := certificate1833
  rw [h.1] at this
  norm_num at this
def C1834 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate1834 : C1834.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1834 : ¬ (C1834.det = 0 ∧ ∀ i, C1834.adjugate i i ≠ 0) := by
  intro h
  have := certificate1834
  rw [h.1] at this
  norm_num at this
def C1835 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate1835 : C1835.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1835 : ¬ (C1835.det = 0 ∧ ∀ i, C1835.adjugate i i ≠ 0) := by
  intro h
  have := certificate1835
  rw [h.1] at this
  norm_num at this
def C1836 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate1836 : C1836.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1836 : ¬ (C1836.det = 0 ∧ ∀ i, C1836.adjugate i i ≠ 0) := by
  intro h
  have := certificate1836
  rw [h.1] at this
  norm_num at this
def C1837 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate1837 : C1837.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1837 : ¬ (C1837.det = 0 ∧ ∀ i, C1837.adjugate i i ≠ 0) := by
  intro h
  have := certificate1837
  rw [h.1] at this
  norm_num at this
def C1838 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate1838 : C1838.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1838 : ¬ (C1838.det = 0 ∧ ∀ i, C1838.adjugate i i ≠ 0) := by
  intro h
  have := certificate1838
  rw [h.1] at this
  norm_num at this
def C1839 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate1839 : C1839.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1839 : ¬ (C1839.det = 0 ∧ ∀ i, C1839.adjugate i i ≠ 0) := by
  intro h
  have := certificate1839
  rw [h.1] at this
  norm_num at this
def C1840 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate1840 : C1840.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1840 : ¬ (C1840.det = 0 ∧ ∀ i, C1840.adjugate i i ≠ 0) := by
  intro h
  have := certificate1840
  rw [h.1] at this
  norm_num at this
def C1841 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate1841 : C1841.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1841 : ¬ (C1841.det = 0 ∧ ∀ i, C1841.adjugate i i ≠ 0) := by
  intro h
  have := certificate1841
  rw [h.1] at this
  norm_num at this
def C1842 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1842 : C1842.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1842 : ¬ (C1842.det = 0 ∧ ∀ i, C1842.adjugate i i ≠ 0) := by
  intro h
  have := certificate1842
  rw [h.1] at this
  norm_num at this
def C1843 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1843 : C1843.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1843 : ¬ (C1843.det = 0 ∧ ∀ i, C1843.adjugate i i ≠ 0) := by
  intro h
  have := certificate1843
  rw [h.1] at this
  norm_num at this
def C1844 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1844 : C1844.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1844 : ¬ (C1844.det = 0 ∧ ∀ i, C1844.adjugate i i ≠ 0) := by
  intro h
  have := certificate1844
  rw [h.1] at this
  norm_num at this
def C1845 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1845 : C1845.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1845 : ¬ (C1845.det = 0 ∧ ∀ i, C1845.adjugate i i ≠ 0) := by
  intro h
  have := certificate1845
  rw [h.1] at this
  norm_num at this
def C1846 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1846 : C1846.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1846 : ¬ (C1846.det = 0 ∧ ∀ i, C1846.adjugate i i ≠ 0) := by
  intro h
  have := certificate1846
  rw [h.1] at this
  norm_num at this
def C1847 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1847 : C1847.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1847 : ¬ (C1847.det = 0 ∧ ∀ i, C1847.adjugate i i ≠ 0) := by
  intro h
  have := certificate1847
  rw [h.1] at this
  norm_num at this
def C1848 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1848 : C1848.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1848 : ¬ (C1848.det = 0 ∧ ∀ i, C1848.adjugate i i ≠ 0) := by
  intro h
  have := certificate1848
  rw [h.1] at this
  norm_num at this
def C1849 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1849 : C1849.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1849 : ¬ (C1849.det = 0 ∧ ∀ i, C1849.adjugate i i ≠ 0) := by
  intro h
  have := certificate1849
  rw [h.1] at this
  norm_num at this
def C1850 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1850 : C1850.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1850 : ¬ (C1850.det = 0 ∧ ∀ i, C1850.adjugate i i ≠ 0) := by
  intro h
  have := certificate1850
  rw [h.1] at this
  norm_num at this
def C1851 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1851 : C1851.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1851 : ¬ (C1851.det = 0 ∧ ∀ i, C1851.adjugate i i ≠ 0) := by
  intro h
  have := certificate1851
  rw [h.1] at this
  norm_num at this
def C1852 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1852 : C1852.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1852 : ¬ (C1852.det = 0 ∧ ∀ i, C1852.adjugate i i ≠ 0) := by
  intro h
  have := certificate1852
  rw [h.1] at this
  norm_num at this
def C1853 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1853 : C1853.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1853 : ¬ (C1853.det = 0 ∧ ∀ i, C1853.adjugate i i ≠ 0) := by
  intro h
  have := certificate1853
  rw [h.1] at this
  norm_num at this
def C1854 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1854 : C1854.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1854 : ¬ (C1854.det = 0 ∧ ∀ i, C1854.adjugate i i ≠ 0) := by
  intro h
  have := certificate1854
  rw [h.1] at this
  norm_num at this
def C1855 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1855 : C1855.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1855 : ¬ (C1855.det = 0 ∧ ∀ i, C1855.adjugate i i ≠ 0) := by
  intro h
  have := certificate1855
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0057
