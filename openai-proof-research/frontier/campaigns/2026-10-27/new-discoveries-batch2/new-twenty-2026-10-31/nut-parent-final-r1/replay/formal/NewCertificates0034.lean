import VerifiedDet
namespace Nut8.NewCertificates0034
def C1088 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1088 : C1088.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1088 : ¬ (C1088.det = 0 ∧ ∀ i, C1088.adjugate i i ≠ 0) := by
  intro h
  have := certificate1088
  rw [h.1] at this
  norm_num at this
def C1089 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1089 : C1089.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1089 : ¬ (C1089.det = 0 ∧ ∀ i, C1089.adjugate i i ≠ 0) := by
  intro h
  have := certificate1089
  rw [h.1] at this
  norm_num at this
def C1090 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1090 : C1090.det = (-43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1090 : ¬ (C1090.det = 0 ∧ ∀ i, C1090.adjugate i i ≠ 0) := by
  intro h
  have := certificate1090
  rw [h.1] at this
  norm_num at this
def C1091 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1091 : C1091.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1091 : ¬ (C1091.det = 0 ∧ ∀ i, C1091.adjugate i i ≠ 0) := by
  intro h
  have := certificate1091
  rw [h.1] at this
  norm_num at this
def C1092 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1092 : C1092.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1092 : ¬ (C1092.det = 0 ∧ ∀ i, C1092.adjugate i i ≠ 0) := by
  intro h
  have := certificate1092
  rw [h.1] at this
  norm_num at this
def C1093 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1093 : C1093.det = (-43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1093 : ¬ (C1093.det = 0 ∧ ∀ i, C1093.adjugate i i ≠ 0) := by
  intro h
  have := certificate1093
  rw [h.1] at this
  norm_num at this
def C1094 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1094 : C1094.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1094 : ¬ (C1094.det = 0 ∧ ∀ i, C1094.adjugate i i ≠ 0) := by
  intro h
  have := certificate1094
  rw [h.1] at this
  norm_num at this
def C1095 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1095 : C1095.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1095 : ¬ (C1095.det = 0 ∧ ∀ i, C1095.adjugate i i ≠ 0) := by
  intro h
  have := certificate1095
  rw [h.1] at this
  norm_num at this
def C1096 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1096 : C1096.det = (-105 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1096 : ¬ (C1096.det = 0 ∧ ∀ i, C1096.adjugate i i ≠ 0) := by
  intro h
  have := certificate1096
  rw [h.1] at this
  norm_num at this
def C1097 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1097 : C1097.det = (55 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1097 : ¬ (C1097.det = 0 ∧ ∀ i, C1097.adjugate i i ≠ 0) := by
  intro h
  have := certificate1097
  rw [h.1] at this
  norm_num at this
def C1098 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1098 : C1098.det = (55 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1098 : ¬ (C1098.det = 0 ∧ ∀ i, C1098.adjugate i i ≠ 0) := by
  intro h
  have := certificate1098
  rw [h.1] at this
  norm_num at this
def C1099 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1099 : C1099.det = (-105 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1099 : ¬ (C1099.det = 0 ∧ ∀ i, C1099.adjugate i i ≠ 0) := by
  intro h
  have := certificate1099
  rw [h.1] at this
  norm_num at this
def C1100 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1100 : C1100.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1100 : ¬ (C1100.det = 0 ∧ ∀ i, C1100.adjugate i i ≠ 0) := by
  intro h
  have := certificate1100
  rw [h.1] at this
  norm_num at this
def C1101 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1101 : C1101.det = (-38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1101 : ¬ (C1101.det = 0 ∧ ∀ i, C1101.adjugate i i ≠ 0) := by
  intro h
  have := certificate1101
  rw [h.1] at this
  norm_num at this
def C1102 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1102 : C1102.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1102 : ¬ (C1102.det = 0 ∧ ∀ i, C1102.adjugate i i ≠ 0) := by
  intro h
  have := certificate1102
  rw [h.1] at this
  norm_num at this
def C1103 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1103 : C1103.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1103 : ¬ (C1103.det = 0 ∧ ∀ i, C1103.adjugate i i ≠ 0) := by
  intro h
  have := certificate1103
  rw [h.1] at this
  norm_num at this
def C1104 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1104 : C1104.det = (-58 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1104 : ¬ (C1104.det = 0 ∧ ∀ i, C1104.adjugate i i ≠ 0) := by
  intro h
  have := certificate1104
  rw [h.1] at this
  norm_num at this
def C1105 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1105 : C1105.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1105 : ¬ (C1105.det = 0 ∧ ∀ i, C1105.adjugate i i ≠ 0) := by
  intro h
  have := certificate1105
  rw [h.1] at this
  norm_num at this
def C1106 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1106 : C1106.det = (54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1106 : ¬ (C1106.det = 0 ∧ ∀ i, C1106.adjugate i i ≠ 0) := by
  intro h
  have := certificate1106
  rw [h.1] at this
  norm_num at this
def C1107 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1107 : C1107.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1107 : ¬ (C1107.det = 0 ∧ ∀ i, C1107.adjugate i i ≠ 0) := by
  intro h
  have := certificate1107
  rw [h.1] at this
  norm_num at this
def C1108 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1108 : C1108.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1108 : ¬ (C1108.det = 0 ∧ ∀ i, C1108.adjugate i i ≠ 0) := by
  intro h
  have := certificate1108
  rw [h.1] at this
  norm_num at this
def C1109 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1109 : C1109.det = (54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1109 : ¬ (C1109.det = 0 ∧ ∀ i, C1109.adjugate i i ≠ 0) := by
  intro h
  have := certificate1109
  rw [h.1] at this
  norm_num at this
def C1110 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1110 : C1110.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1110 : ¬ (C1110.det = 0 ∧ ∀ i, C1110.adjugate i i ≠ 0) := by
  intro h
  have := certificate1110
  rw [h.1] at this
  norm_num at this
def C1111 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1111 : C1111.det = (-58 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1111 : ¬ (C1111.det = 0 ∧ ∀ i, C1111.adjugate i i ≠ 0) := by
  intro h
  have := certificate1111
  rw [h.1] at this
  norm_num at this
def C1112 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1112 : C1112.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1112 : ¬ (C1112.det = 0 ∧ ∀ i, C1112.adjugate i i ≠ 0) := by
  intro h
  have := certificate1112
  rw [h.1] at this
  norm_num at this
def C1113 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1113 : C1113.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1113 : ¬ (C1113.det = 0 ∧ ∀ i, C1113.adjugate i i ≠ 0) := by
  intro h
  have := certificate1113
  rw [h.1] at this
  norm_num at this
def C1114 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1114 : C1114.det = (-38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1114 : ¬ (C1114.det = 0 ∧ ∀ i, C1114.adjugate i i ≠ 0) := by
  intro h
  have := certificate1114
  rw [h.1] at this
  norm_num at this
def C1115 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1115 : C1115.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1115 : ¬ (C1115.det = 0 ∧ ∀ i, C1115.adjugate i i ≠ 0) := by
  intro h
  have := certificate1115
  rw [h.1] at this
  norm_num at this
def C1116 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1116 : C1116.det = (-114 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1116 : ¬ (C1116.det = 0 ∧ ∀ i, C1116.adjugate i i ≠ 0) := by
  intro h
  have := certificate1116
  rw [h.1] at this
  norm_num at this
def C1117 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1117 : C1117.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1117 : ¬ (C1117.det = 0 ∧ ∀ i, C1117.adjugate i i ≠ 0) := by
  intro h
  have := certificate1117
  rw [h.1] at this
  norm_num at this
def C1118 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1118 : C1118.det = (94 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1118 : ¬ (C1118.det = 0 ∧ ∀ i, C1118.adjugate i i ≠ 0) := by
  intro h
  have := certificate1118
  rw [h.1] at this
  norm_num at this
def C1119 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1119 : C1119.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1119 : ¬ (C1119.det = 0 ∧ ∀ i, C1119.adjugate i i ≠ 0) := by
  intro h
  have := certificate1119
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0034
