import VerifiedDet
namespace Nut8.NewCertificates0061
def C1952 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate1952 : C1952.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1952 : ¬ (C1952.det = 0 ∧ ∀ i, C1952.adjugate i i ≠ 0) := by
  intro h
  have := certificate1952
  rw [h.1] at this
  norm_num at this
def C1953 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate1953 : C1953.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1953 : ¬ (C1953.det = 0 ∧ ∀ i, C1953.adjugate i i ≠ 0) := by
  intro h
  have := certificate1953
  rw [h.1] at this
  norm_num at this
def C1954 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1954 : C1954.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1954 : ¬ (C1954.det = 0 ∧ ∀ i, C1954.adjugate i i ≠ 0) := by
  intro h
  have := certificate1954
  rw [h.1] at this
  norm_num at this
def C1955 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1955 : C1955.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1955 : ¬ (C1955.det = 0 ∧ ∀ i, C1955.adjugate i i ≠ 0) := by
  intro h
  have := certificate1955
  rw [h.1] at this
  norm_num at this
def C1956 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1956 : C1956.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1956 : ¬ (C1956.det = 0 ∧ ∀ i, C1956.adjugate i i ≠ 0) := by
  intro h
  have := certificate1956
  rw [h.1] at this
  norm_num at this
def C1957 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1957 : C1957.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1957 : ¬ (C1957.det = 0 ∧ ∀ i, C1957.adjugate i i ≠ 0) := by
  intro h
  have := certificate1957
  rw [h.1] at this
  norm_num at this
def C1958 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1958 : C1958.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1958 : ¬ (C1958.det = 0 ∧ ∀ i, C1958.adjugate i i ≠ 0) := by
  intro h
  have := certificate1958
  rw [h.1] at this
  norm_num at this
def C1959 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1959 : C1959.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1959 : ¬ (C1959.det = 0 ∧ ∀ i, C1959.adjugate i i ≠ 0) := by
  intro h
  have := certificate1959
  rw [h.1] at this
  norm_num at this
def C1960 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate1960 : C1960.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1960 : ¬ (C1960.det = 0 ∧ ∀ i, C1960.adjugate i i ≠ 0) := by
  intro h
  have := certificate1960
  rw [h.1] at this
  norm_num at this
def C1961 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate1961 : C1961.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1961 : ¬ (C1961.det = 0 ∧ ∀ i, C1961.adjugate i i ≠ 0) := by
  intro h
  have := certificate1961
  rw [h.1] at this
  norm_num at this
def C1962 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1962 : C1962.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1962 : ¬ (C1962.det = 0 ∧ ∀ i, C1962.adjugate i i ≠ 0) := by
  intro h
  have := certificate1962
  rw [h.1] at this
  norm_num at this
def C1963 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1963 : C1963.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1963 : ¬ (C1963.det = 0 ∧ ∀ i, C1963.adjugate i i ≠ 0) := by
  intro h
  have := certificate1963
  rw [h.1] at this
  norm_num at this
def C1964 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1964 : C1964.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1964 : ¬ (C1964.det = 0 ∧ ∀ i, C1964.adjugate i i ≠ 0) := by
  intro h
  have := certificate1964
  rw [h.1] at this
  norm_num at this
def C1965 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1965 : C1965.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1965 : ¬ (C1965.det = 0 ∧ ∀ i, C1965.adjugate i i ≠ 0) := by
  intro h
  have := certificate1965
  rw [h.1] at this
  norm_num at this
def C1966 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1966 : C1966.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1966 : ¬ (C1966.det = 0 ∧ ∀ i, C1966.adjugate i i ≠ 0) := by
  intro h
  have := certificate1966
  rw [h.1] at this
  norm_num at this
def C1967 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1967 : C1967.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1967 : ¬ (C1967.det = 0 ∧ ∀ i, C1967.adjugate i i ≠ 0) := by
  intro h
  have := certificate1967
  rw [h.1] at this
  norm_num at this
def C1968 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1968 : C1968.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1968 : ¬ (C1968.det = 0 ∧ ∀ i, C1968.adjugate i i ≠ 0) := by
  intro h
  have := certificate1968
  rw [h.1] at this
  norm_num at this
def C1969 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1969 : C1969.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1969 : ¬ (C1969.det = 0 ∧ ∀ i, C1969.adjugate i i ≠ 0) := by
  intro h
  have := certificate1969
  rw [h.1] at this
  norm_num at this
def C1970 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1970 : C1970.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1970 : ¬ (C1970.det = 0 ∧ ∀ i, C1970.adjugate i i ≠ 0) := by
  intro h
  have := certificate1970
  rw [h.1] at this
  norm_num at this
def C1971 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1971 : C1971.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1971 : ¬ (C1971.det = 0 ∧ ∀ i, C1971.adjugate i i ≠ 0) := by
  intro h
  have := certificate1971
  rw [h.1] at this
  norm_num at this
def C1972 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1972 : C1972.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1972 : ¬ (C1972.det = 0 ∧ ∀ i, C1972.adjugate i i ≠ 0) := by
  intro h
  have := certificate1972
  rw [h.1] at this
  norm_num at this
def C1973 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1973 : C1973.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1973 : ¬ (C1973.det = 0 ∧ ∀ i, C1973.adjugate i i ≠ 0) := by
  intro h
  have := certificate1973
  rw [h.1] at this
  norm_num at this
def C1974 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1974 : C1974.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1974 : ¬ (C1974.det = 0 ∧ ∀ i, C1974.adjugate i i ≠ 0) := by
  intro h
  have := certificate1974
  rw [h.1] at this
  norm_num at this
def C1975 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1975 : C1975.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1975 : ¬ (C1975.det = 0 ∧ ∀ i, C1975.adjugate i i ≠ 0) := by
  intro h
  have := certificate1975
  rw [h.1] at this
  norm_num at this
def C1976 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1976 : C1976.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1976 : ¬ (C1976.det = 0 ∧ ∀ i, C1976.adjugate i i ≠ 0) := by
  intro h
  have := certificate1976
  rw [h.1] at this
  norm_num at this
def C1977 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1977 : C1977.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1977 : ¬ (C1977.det = 0 ∧ ∀ i, C1977.adjugate i i ≠ 0) := by
  intro h
  have := certificate1977
  rw [h.1] at this
  norm_num at this
def C1978 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1978 : C1978.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1978 : ¬ (C1978.det = 0 ∧ ∀ i, C1978.adjugate i i ≠ 0) := by
  intro h
  have := certificate1978
  rw [h.1] at this
  norm_num at this
def C1979 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1979 : C1979.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1979 : ¬ (C1979.det = 0 ∧ ∀ i, C1979.adjugate i i ≠ 0) := by
  intro h
  have := certificate1979
  rw [h.1] at this
  norm_num at this
def C1980 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1980 : C1980.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1980 : ¬ (C1980.det = 0 ∧ ∀ i, C1980.adjugate i i ≠ 0) := by
  intro h
  have := certificate1980
  rw [h.1] at this
  norm_num at this
def C1981 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1981 : C1981.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1981 : ¬ (C1981.det = 0 ∧ ∀ i, C1981.adjugate i i ≠ 0) := by
  intro h
  have := certificate1981
  rw [h.1] at this
  norm_num at this
def C1982 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1982 : C1982.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1982 : ¬ (C1982.det = 0 ∧ ∀ i, C1982.adjugate i i ≠ 0) := by
  intro h
  have := certificate1982
  rw [h.1] at this
  norm_num at this
def C1983 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1983 : C1983.det = (37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1983 : ¬ (C1983.det = 0 ∧ ∀ i, C1983.adjugate i i ≠ 0) := by
  intro h
  have := certificate1983
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0061
