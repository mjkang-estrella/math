import VerifiedDet
namespace Nut8.NewCertificates0033
def C1056 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1056 : C1056.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1056 : ¬ (C1056.det = 0 ∧ ∀ i, C1056.adjugate i i ≠ 0) := by
  intro h
  have := certificate1056
  rw [h.1] at this
  norm_num at this
def C1057 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1057 : C1057.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1057 : ¬ (C1057.det = 0 ∧ ∀ i, C1057.adjugate i i ≠ 0) := by
  intro h
  have := certificate1057
  rw [h.1] at this
  norm_num at this
def C1058 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1058 : C1058.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1058 : ¬ (C1058.det = 0 ∧ ∀ i, C1058.adjugate i i ≠ 0) := by
  intro h
  have := certificate1058
  rw [h.1] at this
  norm_num at this
def C1059 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1059 : C1059.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1059 : ¬ (C1059.det = 0 ∧ ∀ i, C1059.adjugate i i ≠ 0) := by
  intro h
  have := certificate1059
  rw [h.1] at this
  norm_num at this
def C1060 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1060 : C1060.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1060 : ¬ (C1060.det = 0 ∧ ∀ i, C1060.adjugate i i ≠ 0) := by
  intro h
  have := certificate1060
  rw [h.1] at this
  norm_num at this
def C1061 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate1061 : C1061.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1061 : ¬ (C1061.det = 0 ∧ ∀ i, C1061.adjugate i i ≠ 0) := by
  intro h
  have := certificate1061
  rw [h.1] at this
  norm_num at this
def C1062 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1062 : C1062.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1062 : ¬ (C1062.det = 0 ∧ ∀ i, C1062.adjugate i i ≠ 0) := by
  intro h
  have := certificate1062
  rw [h.1] at this
  norm_num at this
def C1063 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate1063 : C1063.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1063 : ¬ (C1063.det = 0 ∧ ∀ i, C1063.adjugate i i ≠ 0) := by
  intro h
  have := certificate1063
  rw [h.1] at this
  norm_num at this
def C1064 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1064 : C1064.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1064 : ¬ (C1064.det = 0 ∧ ∀ i, C1064.adjugate i i ≠ 0) := by
  intro h
  have := certificate1064
  rw [h.1] at this
  norm_num at this
def C1065 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1065 : C1065.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1065 : ¬ (C1065.det = 0 ∧ ∀ i, C1065.adjugate i i ≠ 0) := by
  intro h
  have := certificate1065
  rw [h.1] at this
  norm_num at this
def C1066 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1066 : C1066.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1066 : ¬ (C1066.det = 0 ∧ ∀ i, C1066.adjugate i i ≠ 0) := by
  intro h
  have := certificate1066
  rw [h.1] at this
  norm_num at this
def C1067 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1067 : C1067.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1067 : ¬ (C1067.det = 0 ∧ ∀ i, C1067.adjugate i i ≠ 0) := by
  intro h
  have := certificate1067
  rw [h.1] at this
  norm_num at this
def C1068 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1068 : C1068.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1068 : ¬ (C1068.det = 0 ∧ ∀ i, C1068.adjugate i i ≠ 0) := by
  intro h
  have := certificate1068
  rw [h.1] at this
  norm_num at this
def C1069 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1069 : C1069.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1069 : ¬ (C1069.det = 0 ∧ ∀ i, C1069.adjugate i i ≠ 0) := by
  intro h
  have := certificate1069
  rw [h.1] at this
  norm_num at this
def C1070 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1070 : C1070.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1070 : ¬ (C1070.det = 0 ∧ ∀ i, C1070.adjugate i i ≠ 0) := by
  intro h
  have := certificate1070
  rw [h.1] at this
  norm_num at this
def C1071 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1071 : C1071.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1071 : ¬ (C1071.det = 0 ∧ ∀ i, C1071.adjugate i i ≠ 0) := by
  intro h
  have := certificate1071
  rw [h.1] at this
  norm_num at this
def C1072 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1072 : C1072.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1072 : ¬ (C1072.det = 0 ∧ ∀ i, C1072.adjugate i i ≠ 0) := by
  intro h
  have := certificate1072
  rw [h.1] at this
  norm_num at this
def C1073 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1073 : C1073.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1073 : ¬ (C1073.det = 0 ∧ ∀ i, C1073.adjugate i i ≠ 0) := by
  intro h
  have := certificate1073
  rw [h.1] at this
  norm_num at this
def C1074 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1074 : C1074.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1074 : ¬ (C1074.det = 0 ∧ ∀ i, C1074.adjugate i i ≠ 0) := by
  intro h
  have := certificate1074
  rw [h.1] at this
  norm_num at this
def C1075 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1075 : C1075.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1075 : ¬ (C1075.det = 0 ∧ ∀ i, C1075.adjugate i i ≠ 0) := by
  intro h
  have := certificate1075
  rw [h.1] at this
  norm_num at this
def C1076 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1076 : C1076.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1076 : ¬ (C1076.det = 0 ∧ ∀ i, C1076.adjugate i i ≠ 0) := by
  intro h
  have := certificate1076
  rw [h.1] at this
  norm_num at this
def C1077 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1077 : C1077.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1077 : ¬ (C1077.det = 0 ∧ ∀ i, C1077.adjugate i i ≠ 0) := by
  intro h
  have := certificate1077
  rw [h.1] at this
  norm_num at this
def C1078 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1078 : C1078.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1078 : ¬ (C1078.det = 0 ∧ ∀ i, C1078.adjugate i i ≠ 0) := by
  intro h
  have := certificate1078
  rw [h.1] at this
  norm_num at this
def C1079 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1079 : C1079.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1079 : ¬ (C1079.det = 0 ∧ ∀ i, C1079.adjugate i i ≠ 0) := by
  intro h
  have := certificate1079
  rw [h.1] at this
  norm_num at this
def C1080 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1080 : C1080.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1080 : ¬ (C1080.det = 0 ∧ ∀ i, C1080.adjugate i i ≠ 0) := by
  intro h
  have := certificate1080
  rw [h.1] at this
  norm_num at this
def C1081 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1081 : C1081.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1081 : ¬ (C1081.det = 0 ∧ ∀ i, C1081.adjugate i i ≠ 0) := by
  intro h
  have := certificate1081
  rw [h.1] at this
  norm_num at this
def C1082 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1082 : C1082.det = (-43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1082 : ¬ (C1082.det = 0 ∧ ∀ i, C1082.adjugate i i ≠ 0) := by
  intro h
  have := certificate1082
  rw [h.1] at this
  norm_num at this
def C1083 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1083 : C1083.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1083 : ¬ (C1083.det = 0 ∧ ∀ i, C1083.adjugate i i ≠ 0) := by
  intro h
  have := certificate1083
  rw [h.1] at this
  norm_num at this
def C1084 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1084 : C1084.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1084 : ¬ (C1084.det = 0 ∧ ∀ i, C1084.adjugate i i ≠ 0) := by
  intro h
  have := certificate1084
  rw [h.1] at this
  norm_num at this
def C1085 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1085 : C1085.det = (-43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1085 : ¬ (C1085.det = 0 ∧ ∀ i, C1085.adjugate i i ≠ 0) := by
  intro h
  have := certificate1085
  rw [h.1] at this
  norm_num at this
def C1086 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1086 : C1086.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1086 : ¬ (C1086.det = 0 ∧ ∀ i, C1086.adjugate i i ≠ 0) := by
  intro h
  have := certificate1086
  rw [h.1] at this
  norm_num at this
def C1087 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1087 : C1087.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1087 : ¬ (C1087.det = 0 ∧ ∀ i, C1087.adjugate i i ≠ 0) := by
  intro h
  have := certificate1087
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0033
