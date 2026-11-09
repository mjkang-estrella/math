import VerifiedDet
namespace Nut8.NewCertificates0059
def C1888 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1888 : C1888.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1888 : ¬ (C1888.det = 0 ∧ ∀ i, C1888.adjugate i i ≠ 0) := by
  intro h
  have := certificate1888
  rw [h.1] at this
  norm_num at this
def C1889 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1889 : C1889.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1889 : ¬ (C1889.det = 0 ∧ ∀ i, C1889.adjugate i i ≠ 0) := by
  intro h
  have := certificate1889
  rw [h.1] at this
  norm_num at this
def C1890 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1890 : C1890.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1890 : ¬ (C1890.det = 0 ∧ ∀ i, C1890.adjugate i i ≠ 0) := by
  intro h
  have := certificate1890
  rw [h.1] at this
  norm_num at this
def C1891 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1891 : C1891.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1891 : ¬ (C1891.det = 0 ∧ ∀ i, C1891.adjugate i i ≠ 0) := by
  intro h
  have := certificate1891
  rw [h.1] at this
  norm_num at this
def C1892 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1892 : C1892.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1892 : ¬ (C1892.det = 0 ∧ ∀ i, C1892.adjugate i i ≠ 0) := by
  intro h
  have := certificate1892
  rw [h.1] at this
  norm_num at this
def C1893 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1893 : C1893.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1893 : ¬ (C1893.det = 0 ∧ ∀ i, C1893.adjugate i i ≠ 0) := by
  intro h
  have := certificate1893
  rw [h.1] at this
  norm_num at this
def C1894 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1894 : C1894.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1894 : ¬ (C1894.det = 0 ∧ ∀ i, C1894.adjugate i i ≠ 0) := by
  intro h
  have := certificate1894
  rw [h.1] at this
  norm_num at this
def C1895 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1895 : C1895.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1895 : ¬ (C1895.det = 0 ∧ ∀ i, C1895.adjugate i i ≠ 0) := by
  intro h
  have := certificate1895
  rw [h.1] at this
  norm_num at this
def C1896 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1896 : C1896.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1896 : ¬ (C1896.det = 0 ∧ ∀ i, C1896.adjugate i i ≠ 0) := by
  intro h
  have := certificate1896
  rw [h.1] at this
  norm_num at this
def C1897 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1897 : C1897.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1897 : ¬ (C1897.det = 0 ∧ ∀ i, C1897.adjugate i i ≠ 0) := by
  intro h
  have := certificate1897
  rw [h.1] at this
  norm_num at this
def C1898 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1898 : C1898.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1898 : ¬ (C1898.det = 0 ∧ ∀ i, C1898.adjugate i i ≠ 0) := by
  intro h
  have := certificate1898
  rw [h.1] at this
  norm_num at this
def C1899 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1899 : C1899.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1899 : ¬ (C1899.det = 0 ∧ ∀ i, C1899.adjugate i i ≠ 0) := by
  intro h
  have := certificate1899
  rw [h.1] at this
  norm_num at this
def C1900 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1900 : C1900.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1900 : ¬ (C1900.det = 0 ∧ ∀ i, C1900.adjugate i i ≠ 0) := by
  intro h
  have := certificate1900
  rw [h.1] at this
  norm_num at this
def C1901 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1901 : C1901.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1901 : ¬ (C1901.det = 0 ∧ ∀ i, C1901.adjugate i i ≠ 0) := by
  intro h
  have := certificate1901
  rw [h.1] at this
  norm_num at this
def C1902 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1902 : C1902.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1902 : ¬ (C1902.det = 0 ∧ ∀ i, C1902.adjugate i i ≠ 0) := by
  intro h
  have := certificate1902
  rw [h.1] at this
  norm_num at this
def C1903 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1903 : C1903.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1903 : ¬ (C1903.det = 0 ∧ ∀ i, C1903.adjugate i i ≠ 0) := by
  intro h
  have := certificate1903
  rw [h.1] at this
  norm_num at this
def C1904 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1904 : C1904.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1904 : ¬ (C1904.det = 0 ∧ ∀ i, C1904.adjugate i i ≠ 0) := by
  intro h
  have := certificate1904
  rw [h.1] at this
  norm_num at this
def C1905 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1905 : C1905.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1905 : ¬ (C1905.det = 0 ∧ ∀ i, C1905.adjugate i i ≠ 0) := by
  intro h
  have := certificate1905
  rw [h.1] at this
  norm_num at this
def C1906 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1906 : C1906.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1906 : ¬ (C1906.det = 0 ∧ ∀ i, C1906.adjugate i i ≠ 0) := by
  intro h
  have := certificate1906
  rw [h.1] at this
  norm_num at this
def C1907 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1907 : C1907.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1907 : ¬ (C1907.det = 0 ∧ ∀ i, C1907.adjugate i i ≠ 0) := by
  intro h
  have := certificate1907
  rw [h.1] at this
  norm_num at this
def C1908 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1908 : C1908.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1908 : ¬ (C1908.det = 0 ∧ ∀ i, C1908.adjugate i i ≠ 0) := by
  intro h
  have := certificate1908
  rw [h.1] at this
  norm_num at this
def C1909 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1909 : C1909.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1909 : ¬ (C1909.det = 0 ∧ ∀ i, C1909.adjugate i i ≠ 0) := by
  intro h
  have := certificate1909
  rw [h.1] at this
  norm_num at this
def C1910 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1910 : C1910.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1910 : ¬ (C1910.det = 0 ∧ ∀ i, C1910.adjugate i i ≠ 0) := by
  intro h
  have := certificate1910
  rw [h.1] at this
  norm_num at this
def C1911 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1911 : C1911.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1911 : ¬ (C1911.det = 0 ∧ ∀ i, C1911.adjugate i i ≠ 0) := by
  intro h
  have := certificate1911
  rw [h.1] at this
  norm_num at this
def C1912 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1912 : C1912.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1912 : ¬ (C1912.det = 0 ∧ ∀ i, C1912.adjugate i i ≠ 0) := by
  intro h
  have := certificate1912
  rw [h.1] at this
  norm_num at this
def C1913 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1913 : C1913.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1913 : ¬ (C1913.det = 0 ∧ ∀ i, C1913.adjugate i i ≠ 0) := by
  intro h
  have := certificate1913
  rw [h.1] at this
  norm_num at this
def C1914 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1914 : C1914.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1914 : ¬ (C1914.det = 0 ∧ ∀ i, C1914.adjugate i i ≠ 0) := by
  intro h
  have := certificate1914
  rw [h.1] at this
  norm_num at this
def C1915 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1915 : C1915.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1915 : ¬ (C1915.det = 0 ∧ ∀ i, C1915.adjugate i i ≠ 0) := by
  intro h
  have := certificate1915
  rw [h.1] at this
  norm_num at this
def C1916 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1916 : C1916.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1916 : ¬ (C1916.det = 0 ∧ ∀ i, C1916.adjugate i i ≠ 0) := by
  intro h
  have := certificate1916
  rw [h.1] at this
  norm_num at this
def C1917 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1917 : C1917.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1917 : ¬ (C1917.det = 0 ∧ ∀ i, C1917.adjugate i i ≠ 0) := by
  intro h
  have := certificate1917
  rw [h.1] at this
  norm_num at this
def C1918 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1918 : C1918.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1918 : ¬ (C1918.det = 0 ∧ ∀ i, C1918.adjugate i i ≠ 0) := by
  intro h
  have := certificate1918
  rw [h.1] at this
  norm_num at this
def C1919 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1919 : C1919.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1919 : ¬ (C1919.det = 0 ∧ ∀ i, C1919.adjugate i i ≠ 0) := by
  intro h
  have := certificate1919
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0059
