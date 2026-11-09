import VerifiedDet
namespace Nut8.NewCertificates0032
def C1024 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate1024 : C1024.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1024 : ¬ (C1024.det = 0 ∧ ∀ i, C1024.adjugate i i ≠ 0) := by
  intro h
  have := certificate1024
  rw [h.1] at this
  norm_num at this
def C1025 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate1025 : C1025.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1025 : ¬ (C1025.det = 0 ∧ ∀ i, C1025.adjugate i i ≠ 0) := by
  intro h
  have := certificate1025
  rw [h.1] at this
  norm_num at this
def C1026 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate1026 : C1026.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1026 : ¬ (C1026.det = 0 ∧ ∀ i, C1026.adjugate i i ≠ 0) := by
  intro h
  have := certificate1026
  rw [h.1] at this
  norm_num at this
def C1027 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate1027 : C1027.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1027 : ¬ (C1027.det = 0 ∧ ∀ i, C1027.adjugate i i ≠ 0) := by
  intro h
  have := certificate1027
  rw [h.1] at this
  norm_num at this
def C1028 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate1028 : C1028.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1028 : ¬ (C1028.det = 0 ∧ ∀ i, C1028.adjugate i i ≠ 0) := by
  intro h
  have := certificate1028
  rw [h.1] at this
  norm_num at this
def C1029 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate1029 : C1029.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1029 : ¬ (C1029.det = 0 ∧ ∀ i, C1029.adjugate i i ≠ 0) := by
  intro h
  have := certificate1029
  rw [h.1] at this
  norm_num at this
def C1030 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate1030 : C1030.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1030 : ¬ (C1030.det = 0 ∧ ∀ i, C1030.adjugate i i ≠ 0) := by
  intro h
  have := certificate1030
  rw [h.1] at this
  norm_num at this
def C1031 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate1031 : C1031.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1031 : ¬ (C1031.det = 0 ∧ ∀ i, C1031.adjugate i i ≠ 0) := by
  intro h
  have := certificate1031
  rw [h.1] at this
  norm_num at this
def C1032 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1032 : C1032.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1032 : ¬ (C1032.det = 0 ∧ ∀ i, C1032.adjugate i i ≠ 0) := by
  intro h
  have := certificate1032
  rw [h.1] at this
  norm_num at this
def C1033 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1033 : C1033.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1033 : ¬ (C1033.det = 0 ∧ ∀ i, C1033.adjugate i i ≠ 0) := by
  intro h
  have := certificate1033
  rw [h.1] at this
  norm_num at this
def C1034 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1034 : C1034.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1034 : ¬ (C1034.det = 0 ∧ ∀ i, C1034.adjugate i i ≠ 0) := by
  intro h
  have := certificate1034
  rw [h.1] at this
  norm_num at this
def C1035 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1035 : C1035.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1035 : ¬ (C1035.det = 0 ∧ ∀ i, C1035.adjugate i i ≠ 0) := by
  intro h
  have := certificate1035
  rw [h.1] at this
  norm_num at this
def C1036 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1036 : C1036.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1036 : ¬ (C1036.det = 0 ∧ ∀ i, C1036.adjugate i i ≠ 0) := by
  intro h
  have := certificate1036
  rw [h.1] at this
  norm_num at this
def C1037 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1037 : C1037.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1037 : ¬ (C1037.det = 0 ∧ ∀ i, C1037.adjugate i i ≠ 0) := by
  intro h
  have := certificate1037
  rw [h.1] at this
  norm_num at this
def C1038 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1038 : C1038.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1038 : ¬ (C1038.det = 0 ∧ ∀ i, C1038.adjugate i i ≠ 0) := by
  intro h
  have := certificate1038
  rw [h.1] at this
  norm_num at this
def C1039 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1039 : C1039.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1039 : ¬ (C1039.det = 0 ∧ ∀ i, C1039.adjugate i i ≠ 0) := by
  intro h
  have := certificate1039
  rw [h.1] at this
  norm_num at this
def C1040 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1040 : C1040.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1040 : ¬ (C1040.det = 0 ∧ ∀ i, C1040.adjugate i i ≠ 0) := by
  intro h
  have := certificate1040
  rw [h.1] at this
  norm_num at this
def C1041 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1041 : C1041.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1041 : ¬ (C1041.det = 0 ∧ ∀ i, C1041.adjugate i i ≠ 0) := by
  intro h
  have := certificate1041
  rw [h.1] at this
  norm_num at this
def C1042 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1042 : C1042.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1042 : ¬ (C1042.det = 0 ∧ ∀ i, C1042.adjugate i i ≠ 0) := by
  intro h
  have := certificate1042
  rw [h.1] at this
  norm_num at this
def C1043 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1043 : C1043.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1043 : ¬ (C1043.det = 0 ∧ ∀ i, C1043.adjugate i i ≠ 0) := by
  intro h
  have := certificate1043
  rw [h.1] at this
  norm_num at this
def C1044 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1044 : C1044.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1044 : ¬ (C1044.det = 0 ∧ ∀ i, C1044.adjugate i i ≠ 0) := by
  intro h
  have := certificate1044
  rw [h.1] at this
  norm_num at this
def C1045 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1045 : C1045.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1045 : ¬ (C1045.det = 0 ∧ ∀ i, C1045.adjugate i i ≠ 0) := by
  intro h
  have := certificate1045
  rw [h.1] at this
  norm_num at this
def C1046 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1046 : C1046.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1046 : ¬ (C1046.det = 0 ∧ ∀ i, C1046.adjugate i i ≠ 0) := by
  intro h
  have := certificate1046
  rw [h.1] at this
  norm_num at this
def C1047 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1047 : C1047.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1047 : ¬ (C1047.det = 0 ∧ ∀ i, C1047.adjugate i i ≠ 0) := by
  intro h
  have := certificate1047
  rw [h.1] at this
  norm_num at this
def C1048 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1048 : C1048.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1048 : ¬ (C1048.det = 0 ∧ ∀ i, C1048.adjugate i i ≠ 0) := by
  intro h
  have := certificate1048
  rw [h.1] at this
  norm_num at this
def C1049 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1049 : C1049.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1049 : ¬ (C1049.det = 0 ∧ ∀ i, C1049.adjugate i i ≠ 0) := by
  intro h
  have := certificate1049
  rw [h.1] at this
  norm_num at this
def C1050 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1050 : C1050.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1050 : ¬ (C1050.det = 0 ∧ ∀ i, C1050.adjugate i i ≠ 0) := by
  intro h
  have := certificate1050
  rw [h.1] at this
  norm_num at this
def C1051 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1051 : C1051.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1051 : ¬ (C1051.det = 0 ∧ ∀ i, C1051.adjugate i i ≠ 0) := by
  intro h
  have := certificate1051
  rw [h.1] at this
  norm_num at this
def C1052 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1052 : C1052.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1052 : ¬ (C1052.det = 0 ∧ ∀ i, C1052.adjugate i i ≠ 0) := by
  intro h
  have := certificate1052
  rw [h.1] at this
  norm_num at this
def C1053 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1053 : C1053.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1053 : ¬ (C1053.det = 0 ∧ ∀ i, C1053.adjugate i i ≠ 0) := by
  intro h
  have := certificate1053
  rw [h.1] at this
  norm_num at this
def C1054 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1054 : C1054.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1054 : ¬ (C1054.det = 0 ∧ ∀ i, C1054.adjugate i i ≠ 0) := by
  intro h
  have := certificate1054
  rw [h.1] at this
  norm_num at this
def C1055 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1055 : C1055.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1055 : ¬ (C1055.det = 0 ∧ ∀ i, C1055.adjugate i i ≠ 0) := by
  intro h
  have := certificate1055
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0032
