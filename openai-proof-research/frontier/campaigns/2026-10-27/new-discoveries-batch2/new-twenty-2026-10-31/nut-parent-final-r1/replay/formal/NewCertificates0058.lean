import VerifiedDet
namespace Nut8.NewCertificates0058
def C1856 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1856 : C1856.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1856 : ¬ (C1856.det = 0 ∧ ∀ i, C1856.adjugate i i ≠ 0) := by
  intro h
  have := certificate1856
  rw [h.1] at this
  norm_num at this
def C1857 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1857 : C1857.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1857 : ¬ (C1857.det = 0 ∧ ∀ i, C1857.adjugate i i ≠ 0) := by
  intro h
  have := certificate1857
  rw [h.1] at this
  norm_num at this
def C1858 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1858 : C1858.det = (-84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1858 : ¬ (C1858.det = 0 ∧ ∀ i, C1858.adjugate i i ≠ 0) := by
  intro h
  have := certificate1858
  rw [h.1] at this
  norm_num at this
def C1859 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1859 : C1859.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1859 : ¬ (C1859.det = 0 ∧ ∀ i, C1859.adjugate i i ≠ 0) := by
  intro h
  have := certificate1859
  rw [h.1] at this
  norm_num at this
def C1860 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1860 : C1860.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1860 : ¬ (C1860.det = 0 ∧ ∀ i, C1860.adjugate i i ≠ 0) := by
  intro h
  have := certificate1860
  rw [h.1] at this
  norm_num at this
def C1861 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate1861 : C1861.det = (-84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1861 : ¬ (C1861.det = 0 ∧ ∀ i, C1861.adjugate i i ≠ 0) := by
  intro h
  have := certificate1861
  rw [h.1] at this
  norm_num at this
def C1862 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1862 : C1862.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1862 : ¬ (C1862.det = 0 ∧ ∀ i, C1862.adjugate i i ≠ 0) := by
  intro h
  have := certificate1862
  rw [h.1] at this
  norm_num at this
def C1863 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1863 : C1863.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1863 : ¬ (C1863.det = 0 ∧ ∀ i, C1863.adjugate i i ≠ 0) := by
  intro h
  have := certificate1863
  rw [h.1] at this
  norm_num at this
def C1864 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1864 : C1864.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1864 : ¬ (C1864.det = 0 ∧ ∀ i, C1864.adjugate i i ≠ 0) := by
  intro h
  have := certificate1864
  rw [h.1] at this
  norm_num at this
def C1865 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate1865 : C1865.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1865 : ¬ (C1865.det = 0 ∧ ∀ i, C1865.adjugate i i ≠ 0) := by
  intro h
  have := certificate1865
  rw [h.1] at this
  norm_num at this
def C1866 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1866 : C1866.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1866 : ¬ (C1866.det = 0 ∧ ∀ i, C1866.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1866
def C1867 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1867 : C1867.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1867 : ¬ (C1867.det = 0 ∧ ∀ i, C1867.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1867
def C1868 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1868 : C1868.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1868 : ¬ (C1868.det = 0 ∧ ∀ i, C1868.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1868
def C1869 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1869 : C1869.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1869 : ¬ (C1869.det = 0 ∧ ∀ i, C1869.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1869
def C1870 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1870 : C1870.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1870 : ¬ (C1870.det = 0 ∧ ∀ i, C1870.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1870
def C1871 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1871 : C1871.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1871 : ¬ (C1871.det = 0 ∧ ∀ i, C1871.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1871
def C1872 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1872 : C1872.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1872 : ¬ (C1872.det = 0 ∧ ∀ i, C1872.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1872
def C1873 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1873 : C1873.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1873 : ¬ (C1873.det = 0 ∧ ∀ i, C1873.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1873
def C1874 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1874 : C1874.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1874 : ¬ (C1874.det = 0 ∧ ∀ i, C1874.adjugate i i ≠ 0) := by
  intro h
  have := certificate1874
  rw [h.1] at this
  norm_num at this
def C1875 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1875 : C1875.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1875 : ¬ (C1875.det = 0 ∧ ∀ i, C1875.adjugate i i ≠ 0) := by
  intro h
  have := certificate1875
  rw [h.1] at this
  norm_num at this
def C1876 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1876 : C1876.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1876 : ¬ (C1876.det = 0 ∧ ∀ i, C1876.adjugate i i ≠ 0) := by
  intro h
  have := certificate1876
  rw [h.1] at this
  norm_num at this
def C1877 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1877 : C1877.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1877 : ¬ (C1877.det = 0 ∧ ∀ i, C1877.adjugate i i ≠ 0) := by
  intro h
  have := certificate1877
  rw [h.1] at this
  norm_num at this
def C1878 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1878 : C1878.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1878 : ¬ (C1878.det = 0 ∧ ∀ i, C1878.adjugate i i ≠ 0) := by
  intro h
  have := certificate1878
  rw [h.1] at this
  norm_num at this
def C1879 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1879 : C1879.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1879 : ¬ (C1879.det = 0 ∧ ∀ i, C1879.adjugate i i ≠ 0) := by
  intro h
  have := certificate1879
  rw [h.1] at this
  norm_num at this
def C1880 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1880 : C1880.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1880 : ¬ (C1880.det = 0 ∧ ∀ i, C1880.adjugate i i ≠ 0) := by
  intro h
  have := certificate1880
  rw [h.1] at this
  norm_num at this
def C1881 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1881 : C1881.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1881 : ¬ (C1881.det = 0 ∧ ∀ i, C1881.adjugate i i ≠ 0) := by
  intro h
  have := certificate1881
  rw [h.1] at this
  norm_num at this
def C1882 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1882 : C1882.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1882 : ¬ (C1882.det = 0 ∧ ∀ i, C1882.adjugate i i ≠ 0) := by
  intro h
  have := certificate1882
  rw [h.1] at this
  norm_num at this
def C1883 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1883 : C1883.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1883 : ¬ (C1883.det = 0 ∧ ∀ i, C1883.adjugate i i ≠ 0) := by
  intro h
  have := certificate1883
  rw [h.1] at this
  norm_num at this
def C1884 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1884 : C1884.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1884 : ¬ (C1884.det = 0 ∧ ∀ i, C1884.adjugate i i ≠ 0) := by
  intro h
  have := certificate1884
  rw [h.1] at this
  norm_num at this
def C1885 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1885 : C1885.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1885 : ¬ (C1885.det = 0 ∧ ∀ i, C1885.adjugate i i ≠ 0) := by
  intro h
  have := certificate1885
  rw [h.1] at this
  norm_num at this
def C1886 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1886 : C1886.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1886 : ¬ (C1886.det = 0 ∧ ∀ i, C1886.adjugate i i ≠ 0) := by
  intro h
  have := certificate1886
  rw [h.1] at this
  norm_num at this
def C1887 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1887 : C1887.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1887 : ¬ (C1887.det = 0 ∧ ∀ i, C1887.adjugate i i ≠ 0) := by
  intro h
  have := certificate1887
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0058
