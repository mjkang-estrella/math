import VerifiedDet
namespace Nut8.NewCertificates0036
def C1152 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1152 : C1152.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1152 : ¬ (C1152.det = 0 ∧ ∀ i, C1152.adjugate i i ≠ 0) := by
  intro h
  have := certificate1152
  rw [h.1] at this
  norm_num at this
def C1153 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1153 : C1153.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1153 : ¬ (C1153.det = 0 ∧ ∀ i, C1153.adjugate i i ≠ 0) := by
  intro h
  have := certificate1153
  rw [h.1] at this
  norm_num at this
def C1154 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1154 : C1154.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1154 : ¬ (C1154.det = 0 ∧ ∀ i, C1154.adjugate i i ≠ 0) := by
  intro h
  have := certificate1154
  rw [h.1] at this
  norm_num at this
def C1155 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1155 : C1155.det = (-96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1155 : ¬ (C1155.det = 0 ∧ ∀ i, C1155.adjugate i i ≠ 0) := by
  intro h
  have := certificate1155
  rw [h.1] at this
  norm_num at this
def C1156 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1156 : C1156.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1156 : ¬ (C1156.det = 0 ∧ ∀ i, C1156.adjugate i i ≠ 0) := by
  intro h
  have := certificate1156
  rw [h.1] at this
  norm_num at this
def C1157 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1157 : C1157.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1157 : ¬ (C1157.det = 0 ∧ ∀ i, C1157.adjugate i i ≠ 0) := by
  intro h
  have := certificate1157
  rw [h.1] at this
  norm_num at this
def C1158 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1158 : C1158.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1158 : ¬ (C1158.det = 0 ∧ ∀ i, C1158.adjugate i i ≠ 0) := by
  intro h
  have := certificate1158
  rw [h.1] at this
  norm_num at this
def C1159 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1159 : C1159.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1159 : ¬ (C1159.det = 0 ∧ ∀ i, C1159.adjugate i i ≠ 0) := by
  intro h
  have := certificate1159
  rw [h.1] at this
  norm_num at this
def C1160 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1160 : C1160.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1160 : ¬ (C1160.det = 0 ∧ ∀ i, C1160.adjugate i i ≠ 0) := by
  intro h
  have := certificate1160
  rw [h.1] at this
  norm_num at this
def C1161 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1161 : C1161.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1161 : ¬ (C1161.det = 0 ∧ ∀ i, C1161.adjugate i i ≠ 0) := by
  intro h
  have := certificate1161
  rw [h.1] at this
  norm_num at this
def C1162 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1162 : C1162.det = (39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1162 : ¬ (C1162.det = 0 ∧ ∀ i, C1162.adjugate i i ≠ 0) := by
  intro h
  have := certificate1162
  rw [h.1] at this
  norm_num at this
def C1163 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1163 : C1163.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1163 : ¬ (C1163.det = 0 ∧ ∀ i, C1163.adjugate i i ≠ 0) := by
  intro h
  have := certificate1163
  rw [h.1] at this
  norm_num at this
def C1164 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1164 : C1164.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1164 : ¬ (C1164.det = 0 ∧ ∀ i, C1164.adjugate i i ≠ 0) := by
  intro h
  have := certificate1164
  rw [h.1] at this
  norm_num at this
def C1165 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1165 : C1165.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1165 : ¬ (C1165.det = 0 ∧ ∀ i, C1165.adjugate i i ≠ 0) := by
  intro h
  have := certificate1165
  rw [h.1] at this
  norm_num at this
def C1166 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1166 : C1166.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1166 : ¬ (C1166.det = 0 ∧ ∀ i, C1166.adjugate i i ≠ 0) := by
  intro h
  have := certificate1166
  rw [h.1] at this
  norm_num at this
def C1167 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1167 : C1167.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1167 : ¬ (C1167.det = 0 ∧ ∀ i, C1167.adjugate i i ≠ 0) := by
  intro h
  have := certificate1167
  rw [h.1] at this
  norm_num at this
def C1168 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1168 : C1168.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1168 : ¬ (C1168.det = 0 ∧ ∀ i, C1168.adjugate i i ≠ 0) := by
  intro h
  have := certificate1168
  rw [h.1] at this
  norm_num at this
def C1169 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1169 : C1169.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1169 : ¬ (C1169.det = 0 ∧ ∀ i, C1169.adjugate i i ≠ 0) := by
  intro h
  have := certificate1169
  rw [h.1] at this
  norm_num at this
def C1170 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1170 : C1170.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1170 : ¬ (C1170.det = 0 ∧ ∀ i, C1170.adjugate i i ≠ 0) := by
  intro h
  have := certificate1170
  rw [h.1] at this
  norm_num at this
def C1171 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1171 : C1171.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1171 : ¬ (C1171.det = 0 ∧ ∀ i, C1171.adjugate i i ≠ 0) := by
  intro h
  have := certificate1171
  rw [h.1] at this
  norm_num at this
def C1172 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1172 : C1172.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1172 : ¬ (C1172.det = 0 ∧ ∀ i, C1172.adjugate i i ≠ 0) := by
  intro h
  have := certificate1172
  rw [h.1] at this
  norm_num at this
def C1173 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1173 : C1173.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1173 : ¬ (C1173.det = 0 ∧ ∀ i, C1173.adjugate i i ≠ 0) := by
  intro h
  have := certificate1173
  rw [h.1] at this
  norm_num at this
def C1174 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1174 : C1174.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1174 : ¬ (C1174.det = 0 ∧ ∀ i, C1174.adjugate i i ≠ 0) := by
  intro h
  have := certificate1174
  rw [h.1] at this
  norm_num at this
def C1175 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1175 : C1175.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1175 : ¬ (C1175.det = 0 ∧ ∀ i, C1175.adjugate i i ≠ 0) := by
  intro h
  have := certificate1175
  rw [h.1] at this
  norm_num at this
def C1176 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1176 : C1176.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1176 : ¬ (C1176.det = 0 ∧ ∀ i, C1176.adjugate i i ≠ 0) := by
  intro h
  have := certificate1176
  rw [h.1] at this
  norm_num at this
def C1177 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1177 : C1177.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1177 : ¬ (C1177.det = 0 ∧ ∀ i, C1177.adjugate i i ≠ 0) := by
  intro h
  have := certificate1177
  rw [h.1] at this
  norm_num at this
def C1178 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1178 : C1178.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1178 : ¬ (C1178.det = 0 ∧ ∀ i, C1178.adjugate i i ≠ 0) := by
  intro h
  have := certificate1178
  rw [h.1] at this
  norm_num at this
def C1179 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1179 : C1179.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1179 : ¬ (C1179.det = 0 ∧ ∀ i, C1179.adjugate i i ≠ 0) := by
  intro h
  have := certificate1179
  rw [h.1] at this
  norm_num at this
def C1180 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1180 : C1180.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1180 : ¬ (C1180.det = 0 ∧ ∀ i, C1180.adjugate i i ≠ 0) := by
  intro h
  have := certificate1180
  rw [h.1] at this
  norm_num at this
def C1181 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1181 : C1181.det = (39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1181 : ¬ (C1181.det = 0 ∧ ∀ i, C1181.adjugate i i ≠ 0) := by
  intro h
  have := certificate1181
  rw [h.1] at this
  norm_num at this
def C1182 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1182 : C1182.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1182 : ¬ (C1182.det = 0 ∧ ∀ i, C1182.adjugate i i ≠ 0) := by
  intro h
  have := certificate1182
  rw [h.1] at this
  norm_num at this
def C1183 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1183 : C1183.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1183 : ¬ (C1183.det = 0 ∧ ∀ i, C1183.adjugate i i ≠ 0) := by
  intro h
  have := certificate1183
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0036
