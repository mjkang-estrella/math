import VerifiedDet
namespace Nut8.NewCertificates0035
def C1120 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1120 : C1120.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1120 : ¬ (C1120.det = 0 ∧ ∀ i, C1120.adjugate i i ≠ 0) := by
  intro h
  have := certificate1120
  rw [h.1] at this
  norm_num at this
def C1121 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1121 : C1121.det = (94 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1121 : ¬ (C1121.det = 0 ∧ ∀ i, C1121.adjugate i i ≠ 0) := by
  intro h
  have := certificate1121
  rw [h.1] at this
  norm_num at this
def C1122 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1122 : C1122.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1122 : ¬ (C1122.det = 0 ∧ ∀ i, C1122.adjugate i i ≠ 0) := by
  intro h
  have := certificate1122
  rw [h.1] at this
  norm_num at this
def C1123 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1123 : C1123.det = (-114 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1123 : ¬ (C1123.det = 0 ∧ ∀ i, C1123.adjugate i i ≠ 0) := by
  intro h
  have := certificate1123
  rw [h.1] at this
  norm_num at this
def C1124 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1124 : C1124.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1124 : ¬ (C1124.det = 0 ∧ ∀ i, C1124.adjugate i i ≠ 0) := by
  intro h
  have := certificate1124
  rw [h.1] at this
  norm_num at this
def C1125 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1125 : C1125.det = (-38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1125 : ¬ (C1125.det = 0 ∧ ∀ i, C1125.adjugate i i ≠ 0) := by
  intro h
  have := certificate1125
  rw [h.1] at this
  norm_num at this
def C1126 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1126 : C1126.det = (-58 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1126 : ¬ (C1126.det = 0 ∧ ∀ i, C1126.adjugate i i ≠ 0) := by
  intro h
  have := certificate1126
  rw [h.1] at this
  norm_num at this
def C1127 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1127 : C1127.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1127 : ¬ (C1127.det = 0 ∧ ∀ i, C1127.adjugate i i ≠ 0) := by
  intro h
  have := certificate1127
  rw [h.1] at this
  norm_num at this
def C1128 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1128 : C1128.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1128 : ¬ (C1128.det = 0 ∧ ∀ i, C1128.adjugate i i ≠ 0) := by
  intro h
  have := certificate1128
  rw [h.1] at this
  norm_num at this
def C1129 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1129 : C1129.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1129 : ¬ (C1129.det = 0 ∧ ∀ i, C1129.adjugate i i ≠ 0) := by
  intro h
  have := certificate1129
  rw [h.1] at this
  norm_num at this
def C1130 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1130 : C1130.det = (54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1130 : ¬ (C1130.det = 0 ∧ ∀ i, C1130.adjugate i i ≠ 0) := by
  intro h
  have := certificate1130
  rw [h.1] at this
  norm_num at this
def C1131 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1131 : C1131.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1131 : ¬ (C1131.det = 0 ∧ ∀ i, C1131.adjugate i i ≠ 0) := by
  intro h
  have := certificate1131
  rw [h.1] at this
  norm_num at this
def C1132 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1132 : C1132.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1132 : ¬ (C1132.det = 0 ∧ ∀ i, C1132.adjugate i i ≠ 0) := by
  intro h
  have := certificate1132
  rw [h.1] at this
  norm_num at this
def C1133 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1133 : C1133.det = (54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1133 : ¬ (C1133.det = 0 ∧ ∀ i, C1133.adjugate i i ≠ 0) := by
  intro h
  have := certificate1133
  rw [h.1] at this
  norm_num at this
def C1134 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1134 : C1134.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1134 : ¬ (C1134.det = 0 ∧ ∀ i, C1134.adjugate i i ≠ 0) := by
  intro h
  have := certificate1134
  rw [h.1] at this
  norm_num at this
def C1135 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1135 : C1135.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1135 : ¬ (C1135.det = 0 ∧ ∀ i, C1135.adjugate i i ≠ 0) := by
  intro h
  have := certificate1135
  rw [h.1] at this
  norm_num at this
def C1136 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1136 : C1136.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1136 : ¬ (C1136.det = 0 ∧ ∀ i, C1136.adjugate i i ≠ 0) := by
  intro h
  have := certificate1136
  rw [h.1] at this
  norm_num at this
def C1137 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1137 : C1137.det = (-58 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1137 : ¬ (C1137.det = 0 ∧ ∀ i, C1137.adjugate i i ≠ 0) := by
  intro h
  have := certificate1137
  rw [h.1] at this
  norm_num at this
def C1138 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1138 : C1138.det = (-38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1138 : ¬ (C1138.det = 0 ∧ ∀ i, C1138.adjugate i i ≠ 0) := by
  intro h
  have := certificate1138
  rw [h.1] at this
  norm_num at this
def C1139 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1139 : C1139.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1139 : ¬ (C1139.det = 0 ∧ ∀ i, C1139.adjugate i i ≠ 0) := by
  intro h
  have := certificate1139
  rw [h.1] at this
  norm_num at this
def C1140 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1140 : C1140.det = (-114 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1140 : ¬ (C1140.det = 0 ∧ ∀ i, C1140.adjugate i i ≠ 0) := by
  intro h
  have := certificate1140
  rw [h.1] at this
  norm_num at this
def C1141 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1141 : C1141.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1141 : ¬ (C1141.det = 0 ∧ ∀ i, C1141.adjugate i i ≠ 0) := by
  intro h
  have := certificate1141
  rw [h.1] at this
  norm_num at this
def C1142 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1142 : C1142.det = (94 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1142 : ¬ (C1142.det = 0 ∧ ∀ i, C1142.adjugate i i ≠ 0) := by
  intro h
  have := certificate1142
  rw [h.1] at this
  norm_num at this
def C1143 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1143 : C1143.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1143 : ¬ (C1143.det = 0 ∧ ∀ i, C1143.adjugate i i ≠ 0) := by
  intro h
  have := certificate1143
  rw [h.1] at this
  norm_num at this
def C1144 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1144 : C1144.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1144 : ¬ (C1144.det = 0 ∧ ∀ i, C1144.adjugate i i ≠ 0) := by
  intro h
  have := certificate1144
  rw [h.1] at this
  norm_num at this
def C1145 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1145 : C1145.det = (94 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1145 : ¬ (C1145.det = 0 ∧ ∀ i, C1145.adjugate i i ≠ 0) := by
  intro h
  have := certificate1145
  rw [h.1] at this
  norm_num at this
def C1146 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate1146 : C1146.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1146 : ¬ (C1146.det = 0 ∧ ∀ i, C1146.adjugate i i ≠ 0) := by
  intro h
  have := certificate1146
  rw [h.1] at this
  norm_num at this
def C1147 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate1147 : C1147.det = (-114 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1147 : ¬ (C1147.det = 0 ∧ ∀ i, C1147.adjugate i i ≠ 0) := by
  intro h
  have := certificate1147
  rw [h.1] at this
  norm_num at this
def C1148 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1148 : C1148.det = (-96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1148 : ¬ (C1148.det = 0 ∧ ∀ i, C1148.adjugate i i ≠ 0) := by
  intro h
  have := certificate1148
  rw [h.1] at this
  norm_num at this
def C1149 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1149 : C1149.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1149 : ¬ (C1149.det = 0 ∧ ∀ i, C1149.adjugate i i ≠ 0) := by
  intro h
  have := certificate1149
  rw [h.1] at this
  norm_num at this
def C1150 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1150 : C1150.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1150 : ¬ (C1150.det = 0 ∧ ∀ i, C1150.adjugate i i ≠ 0) := by
  intro h
  have := certificate1150
  rw [h.1] at this
  norm_num at this
def C1151 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1151 : C1151.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1151 : ¬ (C1151.det = 0 ∧ ∀ i, C1151.adjugate i i ≠ 0) := by
  intro h
  have := certificate1151
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0035
