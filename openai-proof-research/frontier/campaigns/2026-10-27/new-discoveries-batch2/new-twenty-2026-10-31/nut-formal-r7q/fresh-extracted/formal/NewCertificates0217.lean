import VerifiedDet
namespace Nut8.NewCertificates0217
def C6944 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6944 : C6944.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6944 : ¬ (C6944.det = 0 ∧ ∀ i, C6944.adjugate i i ≠ 0) := by
  intro h
  have := certificate6944
  rw [h.1] at this
  norm_num at this
def C6945 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6945 : C6945.det = (41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6945 : ¬ (C6945.det = 0 ∧ ∀ i, C6945.adjugate i i ≠ 0) := by
  intro h
  have := certificate6945
  rw [h.1] at this
  norm_num at this
def C6946 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6946 : C6946.det = (41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6946 : ¬ (C6946.det = 0 ∧ ∀ i, C6946.adjugate i i ≠ 0) := by
  intro h
  have := certificate6946
  rw [h.1] at this
  norm_num at this
def C6947 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6947 : C6947.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6947 : ¬ (C6947.det = 0 ∧ ∀ i, C6947.adjugate i i ≠ 0) := by
  intro h
  have := certificate6947
  rw [h.1] at this
  norm_num at this
def C6948 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6948 : C6948.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6948 : ¬ (C6948.det = 0 ∧ ∀ i, C6948.adjugate i i ≠ 0) := by
  intro h
  have := certificate6948
  rw [h.1] at this
  norm_num at this
def C6949 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6949 : C6949.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6949 : ¬ (C6949.det = 0 ∧ ∀ i, C6949.adjugate i i ≠ 0) := by
  intro h
  have := certificate6949
  rw [h.1] at this
  norm_num at this
def C6950 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6950 : C6950.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6950 : ¬ (C6950.det = 0 ∧ ∀ i, C6950.adjugate i i ≠ 0) := by
  intro h
  have := certificate6950
  rw [h.1] at this
  norm_num at this
def C6951 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6951 : C6951.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6951 : ¬ (C6951.det = 0 ∧ ∀ i, C6951.adjugate i i ≠ 0) := by
  intro h
  have := certificate6951
  rw [h.1] at this
  norm_num at this
def C6952 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6952 : C6952.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6952 : ¬ (C6952.det = 0 ∧ ∀ i, C6952.adjugate i i ≠ 0) := by
  intro h
  have := certificate6952
  rw [h.1] at this
  norm_num at this
def C6953 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6953 : C6953.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6953 : ¬ (C6953.det = 0 ∧ ∀ i, C6953.adjugate i i ≠ 0) := by
  intro h
  have := certificate6953
  rw [h.1] at this
  norm_num at this
def C6954 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6954 : C6954.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6954 : ¬ (C6954.det = 0 ∧ ∀ i, C6954.adjugate i i ≠ 0) := by
  intro h
  have := certificate6954
  rw [h.1] at this
  norm_num at this
def C6955 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6955 : C6955.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6955 : ¬ (C6955.det = 0 ∧ ∀ i, C6955.adjugate i i ≠ 0) := by
  intro h
  have := certificate6955
  rw [h.1] at this
  norm_num at this
def C6956 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6956 : C6956.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6956 : ¬ (C6956.det = 0 ∧ ∀ i, C6956.adjugate i i ≠ 0) := by
  intro h
  have := certificate6956
  rw [h.1] at this
  norm_num at this
def C6957 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6957 : C6957.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6957 : ¬ (C6957.det = 0 ∧ ∀ i, C6957.adjugate i i ≠ 0) := by
  intro h
  have := certificate6957
  rw [h.1] at this
  norm_num at this
def C6958 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6958 : C6958.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6958 : ¬ (C6958.det = 0 ∧ ∀ i, C6958.adjugate i i ≠ 0) := by
  intro h
  have := certificate6958
  rw [h.1] at this
  norm_num at this
def C6959 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6959 : C6959.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6959 : ¬ (C6959.det = 0 ∧ ∀ i, C6959.adjugate i i ≠ 0) := by
  intro h
  have := certificate6959
  rw [h.1] at this
  norm_num at this
def C6960 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6960 : C6960.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6960 : ¬ (C6960.det = 0 ∧ ∀ i, C6960.adjugate i i ≠ 0) := by
  intro h
  have := certificate6960
  rw [h.1] at this
  norm_num at this
def C6961 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6961 : C6961.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6961 : ¬ (C6961.det = 0 ∧ ∀ i, C6961.adjugate i i ≠ 0) := by
  intro h
  have := certificate6961
  rw [h.1] at this
  norm_num at this
def C6962 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6962 : C6962.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6962 : ¬ (C6962.det = 0 ∧ ∀ i, C6962.adjugate i i ≠ 0) := by
  intro h
  have := certificate6962
  rw [h.1] at this
  norm_num at this
def C6963 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6963 : C6963.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6963 : ¬ (C6963.det = 0 ∧ ∀ i, C6963.adjugate i i ≠ 0) := by
  intro h
  have := certificate6963
  rw [h.1] at this
  norm_num at this
def C6964 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6964 : C6964.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6964 : ¬ (C6964.det = 0 ∧ ∀ i, C6964.adjugate i i ≠ 0) := by
  intro h
  have := certificate6964
  rw [h.1] at this
  norm_num at this
def C6965 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6965 : C6965.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6965 : ¬ (C6965.det = 0 ∧ ∀ i, C6965.adjugate i i ≠ 0) := by
  intro h
  have := certificate6965
  rw [h.1] at this
  norm_num at this
def C6966 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6966 : C6966.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6966 : ¬ (C6966.det = 0 ∧ ∀ i, C6966.adjugate i i ≠ 0) := by
  intro h
  have := certificate6966
  rw [h.1] at this
  norm_num at this
def C6967 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6967 : C6967.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6967 : ¬ (C6967.det = 0 ∧ ∀ i, C6967.adjugate i i ≠ 0) := by
  intro h
  have := certificate6967
  rw [h.1] at this
  norm_num at this
def C6968 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6968 : C6968.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6968 : ¬ (C6968.det = 0 ∧ ∀ i, C6968.adjugate i i ≠ 0) := by
  intro h
  have := certificate6968
  rw [h.1] at this
  norm_num at this
def C6969 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6969 : C6969.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6969 : ¬ (C6969.det = 0 ∧ ∀ i, C6969.adjugate i i ≠ 0) := by
  intro h
  have := certificate6969
  rw [h.1] at this
  norm_num at this
def C6970 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6970 : C6970.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6970 : ¬ (C6970.det = 0 ∧ ∀ i, C6970.adjugate i i ≠ 0) := by
  intro h
  have := certificate6970
  rw [h.1] at this
  norm_num at this
def C6971 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6971 : C6971.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6971 : ¬ (C6971.det = 0 ∧ ∀ i, C6971.adjugate i i ≠ 0) := by
  intro h
  have := certificate6971
  rw [h.1] at this
  norm_num at this
def C6972 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6972 : C6972.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6972 : ¬ (C6972.det = 0 ∧ ∀ i, C6972.adjugate i i ≠ 0) := by
  intro h
  have := certificate6972
  rw [h.1] at this
  norm_num at this
def C6973 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6973 : C6973.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6973 : ¬ (C6973.det = 0 ∧ ∀ i, C6973.adjugate i i ≠ 0) := by
  intro h
  have := certificate6973
  rw [h.1] at this
  norm_num at this
def C6974 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6974 : C6974.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6974 : ¬ (C6974.det = 0 ∧ ∀ i, C6974.adjugate i i ≠ 0) := by
  intro h
  have := certificate6974
  rw [h.1] at this
  norm_num at this
def C6975 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6975 : C6975.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6975 : ¬ (C6975.det = 0 ∧ ∀ i, C6975.adjugate i i ≠ 0) := by
  intro h
  have := certificate6975
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0217
