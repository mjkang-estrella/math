import VerifiedDet
namespace Nut8.NewCertificates0039
def C1248 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1248 : C1248.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1248 : ¬ (C1248.det = 0 ∧ ∀ i, C1248.adjugate i i ≠ 0) := by
  intro h
  have := certificate1248
  rw [h.1] at this
  norm_num at this
def C1249 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1249 : C1249.det = (-23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1249 : ¬ (C1249.det = 0 ∧ ∀ i, C1249.adjugate i i ≠ 0) := by
  intro h
  have := certificate1249
  rw [h.1] at this
  norm_num at this
def C1250 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1250 : C1250.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1250 : ¬ (C1250.det = 0 ∧ ∀ i, C1250.adjugate i i ≠ 0) := by
  intro h
  have := certificate1250
  rw [h.1] at this
  norm_num at this
def C1251 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1251 : C1251.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1251 : ¬ (C1251.det = 0 ∧ ∀ i, C1251.adjugate i i ≠ 0) := by
  intro h
  have := certificate1251
  rw [h.1] at this
  norm_num at this
def C1252 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1252 : C1252.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1252 : ¬ (C1252.det = 0 ∧ ∀ i, C1252.adjugate i i ≠ 0) := by
  intro h
  have := certificate1252
  rw [h.1] at this
  norm_num at this
def C1253 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1253 : C1253.det = (-54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1253 : ¬ (C1253.det = 0 ∧ ∀ i, C1253.adjugate i i ≠ 0) := by
  intro h
  have := certificate1253
  rw [h.1] at this
  norm_num at this
def C1254 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1254 : C1254.det = (-46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1254 : ¬ (C1254.det = 0 ∧ ∀ i, C1254.adjugate i i ≠ 0) := by
  intro h
  have := certificate1254
  rw [h.1] at this
  norm_num at this
def C1255 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1255 : C1255.det = (46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1255 : ¬ (C1255.det = 0 ∧ ∀ i, C1255.adjugate i i ≠ 0) := by
  intro h
  have := certificate1255
  rw [h.1] at this
  norm_num at this
def C1256 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1256 : C1256.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1256 : ¬ (C1256.det = 0 ∧ ∀ i, C1256.adjugate i i ≠ 0) := by
  intro h
  have := certificate1256
  rw [h.1] at this
  norm_num at this
def C1257 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1257 : C1257.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1257 : ¬ (C1257.det = 0 ∧ ∀ i, C1257.adjugate i i ≠ 0) := by
  intro h
  have := certificate1257
  rw [h.1] at this
  norm_num at this
def C1258 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1258 : C1258.det = (90 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1258 : ¬ (C1258.det = 0 ∧ ∀ i, C1258.adjugate i i ≠ 0) := by
  intro h
  have := certificate1258
  rw [h.1] at this
  norm_num at this
def C1259 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1259 : C1259.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1259 : ¬ (C1259.det = 0 ∧ ∀ i, C1259.adjugate i i ≠ 0) := by
  intro h
  have := certificate1259
  rw [h.1] at this
  norm_num at this
def C1260 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1260 : C1260.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1260 : ¬ (C1260.det = 0 ∧ ∀ i, C1260.adjugate i i ≠ 0) := by
  intro h
  have := certificate1260
  rw [h.1] at this
  norm_num at this
def C1261 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1261 : C1261.det = (90 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1261 : ¬ (C1261.det = 0 ∧ ∀ i, C1261.adjugate i i ≠ 0) := by
  intro h
  have := certificate1261
  rw [h.1] at this
  norm_num at this
def C1262 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1262 : C1262.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1262 : ¬ (C1262.det = 0 ∧ ∀ i, C1262.adjugate i i ≠ 0) := by
  intro h
  have := certificate1262
  rw [h.1] at this
  norm_num at this
def C1263 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1263 : C1263.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1263 : ¬ (C1263.det = 0 ∧ ∀ i, C1263.adjugate i i ≠ 0) := by
  intro h
  have := certificate1263
  rw [h.1] at this
  norm_num at this
def C1264 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1264 : C1264.det = (46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1264 : ¬ (C1264.det = 0 ∧ ∀ i, C1264.adjugate i i ≠ 0) := by
  intro h
  have := certificate1264
  rw [h.1] at this
  norm_num at this
def C1265 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1265 : C1265.det = (-46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1265 : ¬ (C1265.det = 0 ∧ ∀ i, C1265.adjugate i i ≠ 0) := by
  intro h
  have := certificate1265
  rw [h.1] at this
  norm_num at this
def C1266 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1266 : C1266.det = (-54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1266 : ¬ (C1266.det = 0 ∧ ∀ i, C1266.adjugate i i ≠ 0) := by
  intro h
  have := certificate1266
  rw [h.1] at this
  norm_num at this
def C1267 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1267 : C1267.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1267 : ¬ (C1267.det = 0 ∧ ∀ i, C1267.adjugate i i ≠ 0) := by
  intro h
  have := certificate1267
  rw [h.1] at this
  norm_num at this
def C1268 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1268 : C1268.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1268 : ¬ (C1268.det = 0 ∧ ∀ i, C1268.adjugate i i ≠ 0) := by
  intro h
  have := certificate1268
  rw [h.1] at this
  norm_num at this
def C1269 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1269 : C1269.det = (-54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1269 : ¬ (C1269.det = 0 ∧ ∀ i, C1269.adjugate i i ≠ 0) := by
  intro h
  have := certificate1269
  rw [h.1] at this
  norm_num at this
def C1270 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1270 : C1270.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1270 : ¬ (C1270.det = 0 ∧ ∀ i, C1270.adjugate i i ≠ 0) := by
  intro h
  have := certificate1270
  rw [h.1] at this
  norm_num at this
def C1271 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1271 : C1271.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1271 : ¬ (C1271.det = 0 ∧ ∀ i, C1271.adjugate i i ≠ 0) := by
  intro h
  have := certificate1271
  rw [h.1] at this
  norm_num at this
def C1272 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1272 : C1272.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1272 : ¬ (C1272.det = 0 ∧ ∀ i, C1272.adjugate i i ≠ 0) := by
  intro h
  have := certificate1272
  rw [h.1] at this
  norm_num at this
def C1273 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1273 : C1273.det = (90 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1273 : ¬ (C1273.det = 0 ∧ ∀ i, C1273.adjugate i i ≠ 0) := by
  intro h
  have := certificate1273
  rw [h.1] at this
  norm_num at this
def C1274 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1274 : C1274.det = (46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1274 : ¬ (C1274.det = 0 ∧ ∀ i, C1274.adjugate i i ≠ 0) := by
  intro h
  have := certificate1274
  rw [h.1] at this
  norm_num at this
def C1275 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1275 : C1275.det = (-46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1275 : ¬ (C1275.det = 0 ∧ ∀ i, C1275.adjugate i i ≠ 0) := by
  intro h
  have := certificate1275
  rw [h.1] at this
  norm_num at this
def C1276 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1276 : C1276.det = (-46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1276 : ¬ (C1276.det = 0 ∧ ∀ i, C1276.adjugate i i ≠ 0) := by
  intro h
  have := certificate1276
  rw [h.1] at this
  norm_num at this
def C1277 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1277 : C1277.det = (46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1277 : ¬ (C1277.det = 0 ∧ ∀ i, C1277.adjugate i i ≠ 0) := by
  intro h
  have := certificate1277
  rw [h.1] at this
  norm_num at this
def C1278 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1278 : C1278.det = (90 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1278 : ¬ (C1278.det = 0 ∧ ∀ i, C1278.adjugate i i ≠ 0) := by
  intro h
  have := certificate1278
  rw [h.1] at this
  norm_num at this
def C1279 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1279 : C1279.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1279 : ¬ (C1279.det = 0 ∧ ∀ i, C1279.adjugate i i ≠ 0) := by
  intro h
  have := certificate1279
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0039
