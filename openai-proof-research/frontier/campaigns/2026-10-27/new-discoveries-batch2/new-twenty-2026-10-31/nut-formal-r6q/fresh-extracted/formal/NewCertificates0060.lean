import VerifiedDet
namespace Nut8.NewCertificates0060
def C1920 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1920 : C1920.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1920 : ¬ (C1920.det = 0 ∧ ∀ i, C1920.adjugate i i ≠ 0) := by
  intro h
  have := certificate1920
  rw [h.1] at this
  norm_num at this
def C1921 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1921 : C1921.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1921 : ¬ (C1921.det = 0 ∧ ∀ i, C1921.adjugate i i ≠ 0) := by
  intro h
  have := certificate1921
  rw [h.1] at this
  norm_num at this
def C1922 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1922 : C1922.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1922 : ¬ (C1922.det = 0 ∧ ∀ i, C1922.adjugate i i ≠ 0) := by
  intro h
  have := certificate1922
  rw [h.1] at this
  norm_num at this
def C1923 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1923 : C1923.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1923 : ¬ (C1923.det = 0 ∧ ∀ i, C1923.adjugate i i ≠ 0) := by
  intro h
  have := certificate1923
  rw [h.1] at this
  norm_num at this
def C1924 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1924 : C1924.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1924 : ¬ (C1924.det = 0 ∧ ∀ i, C1924.adjugate i i ≠ 0) := by
  intro h
  have := certificate1924
  rw [h.1] at this
  norm_num at this
def C1925 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1925 : C1925.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1925 : ¬ (C1925.det = 0 ∧ ∀ i, C1925.adjugate i i ≠ 0) := by
  intro h
  have := certificate1925
  rw [h.1] at this
  norm_num at this
def C1926 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1926 : C1926.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1926 : ¬ (C1926.det = 0 ∧ ∀ i, C1926.adjugate i i ≠ 0) := by
  intro h
  have := certificate1926
  rw [h.1] at this
  norm_num at this
def C1927 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1927 : C1927.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1927 : ¬ (C1927.det = 0 ∧ ∀ i, C1927.adjugate i i ≠ 0) := by
  intro h
  have := certificate1927
  rw [h.1] at this
  norm_num at this
def C1928 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1928 : C1928.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1928 : ¬ (C1928.det = 0 ∧ ∀ i, C1928.adjugate i i ≠ 0) := by
  intro h
  have := certificate1928
  rw [h.1] at this
  norm_num at this
def C1929 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1929 : C1929.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1929 : ¬ (C1929.det = 0 ∧ ∀ i, C1929.adjugate i i ≠ 0) := by
  intro h
  have := certificate1929
  rw [h.1] at this
  norm_num at this
def C1930 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1930 : C1930.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1930 : ¬ (C1930.det = 0 ∧ ∀ i, C1930.adjugate i i ≠ 0) := by
  intro h
  have := certificate1930
  rw [h.1] at this
  norm_num at this
def C1931 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1931 : C1931.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1931 : ¬ (C1931.det = 0 ∧ ∀ i, C1931.adjugate i i ≠ 0) := by
  intro h
  have := certificate1931
  rw [h.1] at this
  norm_num at this
def C1932 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1932 : C1932.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1932 : ¬ (C1932.det = 0 ∧ ∀ i, C1932.adjugate i i ≠ 0) := by
  intro h
  have := certificate1932
  rw [h.1] at this
  norm_num at this
def C1933 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1933 : C1933.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1933 : ¬ (C1933.det = 0 ∧ ∀ i, C1933.adjugate i i ≠ 0) := by
  intro h
  have := certificate1933
  rw [h.1] at this
  norm_num at this
def C1934 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1934 : C1934.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1934 : ¬ (C1934.det = 0 ∧ ∀ i, C1934.adjugate i i ≠ 0) := by
  intro h
  have := certificate1934
  rw [h.1] at this
  norm_num at this
def C1935 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1935 : C1935.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1935 : ¬ (C1935.det = 0 ∧ ∀ i, C1935.adjugate i i ≠ 0) := by
  intro h
  have := certificate1935
  rw [h.1] at this
  norm_num at this
def C1936 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1936 : C1936.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1936 : ¬ (C1936.det = 0 ∧ ∀ i, C1936.adjugate i i ≠ 0) := by
  intro h
  have := certificate1936
  rw [h.1] at this
  norm_num at this
def C1937 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1937 : C1937.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1937 : ¬ (C1937.det = 0 ∧ ∀ i, C1937.adjugate i i ≠ 0) := by
  intro h
  have := certificate1937
  rw [h.1] at this
  norm_num at this
def C1938 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1938 : C1938.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1938 : ¬ (C1938.det = 0 ∧ ∀ i, C1938.adjugate i i ≠ 0) := by
  intro h
  have := certificate1938
  rw [h.1] at this
  norm_num at this
def C1939 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1939 : C1939.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1939 : ¬ (C1939.det = 0 ∧ ∀ i, C1939.adjugate i i ≠ 0) := by
  intro h
  have := certificate1939
  rw [h.1] at this
  norm_num at this
def C1940 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1940 : C1940.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1940 : ¬ (C1940.det = 0 ∧ ∀ i, C1940.adjugate i i ≠ 0) := by
  intro h
  have := certificate1940
  rw [h.1] at this
  norm_num at this
def C1941 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1941 : C1941.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1941 : ¬ (C1941.det = 0 ∧ ∀ i, C1941.adjugate i i ≠ 0) := by
  intro h
  have := certificate1941
  rw [h.1] at this
  norm_num at this
def C1942 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1942 : C1942.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1942 : ¬ (C1942.det = 0 ∧ ∀ i, C1942.adjugate i i ≠ 0) := by
  intro h
  have := certificate1942
  rw [h.1] at this
  norm_num at this
def C1943 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1943 : C1943.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1943 : ¬ (C1943.det = 0 ∧ ∀ i, C1943.adjugate i i ≠ 0) := by
  intro h
  have := certificate1943
  rw [h.1] at this
  norm_num at this
def C1944 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1944 : C1944.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1944 : ¬ (C1944.det = 0 ∧ ∀ i, C1944.adjugate i i ≠ 0) := by
  intro h
  have := certificate1944
  rw [h.1] at this
  norm_num at this
def C1945 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1945 : C1945.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1945 : ¬ (C1945.det = 0 ∧ ∀ i, C1945.adjugate i i ≠ 0) := by
  intro h
  have := certificate1945
  rw [h.1] at this
  norm_num at this
def C1946 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1946 : C1946.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1946 : ¬ (C1946.det = 0 ∧ ∀ i, C1946.adjugate i i ≠ 0) := by
  intro h
  have := certificate1946
  rw [h.1] at this
  norm_num at this
def C1947 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1947 : C1947.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1947 : ¬ (C1947.det = 0 ∧ ∀ i, C1947.adjugate i i ≠ 0) := by
  intro h
  have := certificate1947
  rw [h.1] at this
  norm_num at this
def C1948 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1948 : C1948.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1948 : ¬ (C1948.det = 0 ∧ ∀ i, C1948.adjugate i i ≠ 0) := by
  intro h
  have := certificate1948
  rw [h.1] at this
  norm_num at this
def C1949 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1949 : C1949.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1949 : ¬ (C1949.det = 0 ∧ ∀ i, C1949.adjugate i i ≠ 0) := by
  intro h
  have := certificate1949
  rw [h.1] at this
  norm_num at this
def C1950 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1950 : C1950.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1950 : ¬ (C1950.det = 0 ∧ ∀ i, C1950.adjugate i i ≠ 0) := by
  intro h
  have := certificate1950
  rw [h.1] at this
  norm_num at this
def C1951 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1951 : C1951.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1951 : ¬ (C1951.det = 0 ∧ ∀ i, C1951.adjugate i i ≠ 0) := by
  intro h
  have := certificate1951
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0060
