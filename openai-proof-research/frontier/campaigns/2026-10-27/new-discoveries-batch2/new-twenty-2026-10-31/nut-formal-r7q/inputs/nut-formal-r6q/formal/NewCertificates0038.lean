import VerifiedDet
namespace Nut8.NewCertificates0038
def C1216 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1216 : C1216.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1216 : ¬ (C1216.det = 0 ∧ ∀ i, C1216.adjugate i i ≠ 0) := by
  intro h
  have := certificate1216
  rw [h.1] at this
  norm_num at this
def C1217 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1217 : C1217.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1217 : ¬ (C1217.det = 0 ∧ ∀ i, C1217.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1217
def C1218 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1218 : C1218.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction1218 : ¬ (C1218.det = 0 ∧ ∀ i, C1218.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate1218
def C1219 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1219 : C1219.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1219 : ¬ (C1219.det = 0 ∧ ∀ i, C1219.adjugate i i ≠ 0) := by
  intro h
  have := certificate1219
  rw [h.1] at this
  norm_num at this
def C1220 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1220 : C1220.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1220 : ¬ (C1220.det = 0 ∧ ∀ i, C1220.adjugate i i ≠ 0) := by
  intro h
  have := certificate1220
  rw [h.1] at this
  norm_num at this
def C1221 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1221 : C1221.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1221 : ¬ (C1221.det = 0 ∧ ∀ i, C1221.adjugate i i ≠ 0) := by
  intro h
  have := certificate1221
  rw [h.1] at this
  norm_num at this
def C1222 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1222 : C1222.det = (-23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1222 : ¬ (C1222.det = 0 ∧ ∀ i, C1222.adjugate i i ≠ 0) := by
  intro h
  have := certificate1222
  rw [h.1] at this
  norm_num at this
def C1223 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1223 : C1223.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1223 : ¬ (C1223.det = 0 ∧ ∀ i, C1223.adjugate i i ≠ 0) := by
  intro h
  have := certificate1223
  rw [h.1] at this
  norm_num at this
def C1224 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1224 : C1224.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1224 : ¬ (C1224.det = 0 ∧ ∀ i, C1224.adjugate i i ≠ 0) := by
  intro h
  have := certificate1224
  rw [h.1] at this
  norm_num at this
def C1225 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1225 : C1225.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1225 : ¬ (C1225.det = 0 ∧ ∀ i, C1225.adjugate i i ≠ 0) := by
  intro h
  have := certificate1225
  rw [h.1] at this
  norm_num at this
def C1226 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1226 : C1226.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1226 : ¬ (C1226.det = 0 ∧ ∀ i, C1226.adjugate i i ≠ 0) := by
  intro h
  have := certificate1226
  rw [h.1] at this
  norm_num at this
def C1227 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1227 : C1227.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1227 : ¬ (C1227.det = 0 ∧ ∀ i, C1227.adjugate i i ≠ 0) := by
  intro h
  have := certificate1227
  rw [h.1] at this
  norm_num at this
def C1228 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1228 : C1228.det = (-23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1228 : ¬ (C1228.det = 0 ∧ ∀ i, C1228.adjugate i i ≠ 0) := by
  intro h
  have := certificate1228
  rw [h.1] at this
  norm_num at this
def C1229 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1229 : C1229.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1229 : ¬ (C1229.det = 0 ∧ ∀ i, C1229.adjugate i i ≠ 0) := by
  intro h
  have := certificate1229
  rw [h.1] at this
  norm_num at this
def C1230 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1230 : C1230.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1230 : ¬ (C1230.det = 0 ∧ ∀ i, C1230.adjugate i i ≠ 0) := by
  intro h
  have := certificate1230
  rw [h.1] at this
  norm_num at this
def C1231 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1231 : C1231.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1231 : ¬ (C1231.det = 0 ∧ ∀ i, C1231.adjugate i i ≠ 0) := by
  intro h
  have := certificate1231
  rw [h.1] at this
  norm_num at this
def C1232 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1232 : C1232.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1232 : ¬ (C1232.det = 0 ∧ ∀ i, C1232.adjugate i i ≠ 0) := by
  intro h
  have := certificate1232
  rw [h.1] at this
  norm_num at this
def C1233 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1233 : C1233.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1233 : ¬ (C1233.det = 0 ∧ ∀ i, C1233.adjugate i i ≠ 0) := by
  intro h
  have := certificate1233
  rw [h.1] at this
  norm_num at this
def C1234 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1234 : C1234.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1234 : ¬ (C1234.det = 0 ∧ ∀ i, C1234.adjugate i i ≠ 0) := by
  intro h
  have := certificate1234
  rw [h.1] at this
  norm_num at this
def C1235 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1235 : C1235.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1235 : ¬ (C1235.det = 0 ∧ ∀ i, C1235.adjugate i i ≠ 0) := by
  intro h
  have := certificate1235
  rw [h.1] at this
  norm_num at this
def C1236 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1236 : C1236.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1236 : ¬ (C1236.det = 0 ∧ ∀ i, C1236.adjugate i i ≠ 0) := by
  intro h
  have := certificate1236
  rw [h.1] at this
  norm_num at this
def C1237 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1237 : C1237.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1237 : ¬ (C1237.det = 0 ∧ ∀ i, C1237.adjugate i i ≠ 0) := by
  intro h
  have := certificate1237
  rw [h.1] at this
  norm_num at this
def C1238 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1238 : C1238.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1238 : ¬ (C1238.det = 0 ∧ ∀ i, C1238.adjugate i i ≠ 0) := by
  intro h
  have := certificate1238
  rw [h.1] at this
  norm_num at this
def C1239 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1239 : C1239.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1239 : ¬ (C1239.det = 0 ∧ ∀ i, C1239.adjugate i i ≠ 0) := by
  intro h
  have := certificate1239
  rw [h.1] at this
  norm_num at this
def C1240 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1240 : C1240.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1240 : ¬ (C1240.det = 0 ∧ ∀ i, C1240.adjugate i i ≠ 0) := by
  intro h
  have := certificate1240
  rw [h.1] at this
  norm_num at this
def C1241 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1241 : C1241.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1241 : ¬ (C1241.det = 0 ∧ ∀ i, C1241.adjugate i i ≠ 0) := by
  intro h
  have := certificate1241
  rw [h.1] at this
  norm_num at this
def C1242 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1242 : C1242.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1242 : ¬ (C1242.det = 0 ∧ ∀ i, C1242.adjugate i i ≠ 0) := by
  intro h
  have := certificate1242
  rw [h.1] at this
  norm_num at this
def C1243 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1243 : C1243.det = (-23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1243 : ¬ (C1243.det = 0 ∧ ∀ i, C1243.adjugate i i ≠ 0) := by
  intro h
  have := certificate1243
  rw [h.1] at this
  norm_num at this
def C1244 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1244 : C1244.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1244 : ¬ (C1244.det = 0 ∧ ∀ i, C1244.adjugate i i ≠ 0) := by
  intro h
  have := certificate1244
  rw [h.1] at this
  norm_num at this
def C1245 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1245 : C1245.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1245 : ¬ (C1245.det = 0 ∧ ∀ i, C1245.adjugate i i ≠ 0) := by
  intro h
  have := certificate1245
  rw [h.1] at this
  norm_num at this
def C1246 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1246 : C1246.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1246 : ¬ (C1246.det = 0 ∧ ∀ i, C1246.adjugate i i ≠ 0) := by
  intro h
  have := certificate1246
  rw [h.1] at this
  norm_num at this
def C1247 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1247 : C1247.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1247 : ¬ (C1247.det = 0 ∧ ∀ i, C1247.adjugate i i ≠ 0) := by
  intro h
  have := certificate1247
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0038
