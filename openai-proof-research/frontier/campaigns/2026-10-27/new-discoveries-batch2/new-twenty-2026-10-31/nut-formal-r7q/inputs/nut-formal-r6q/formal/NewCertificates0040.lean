import VerifiedDet
namespace Nut8.NewCertificates0040
def C1280 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1280 : C1280.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1280 : ¬ (C1280.det = 0 ∧ ∀ i, C1280.adjugate i i ≠ 0) := by
  intro h
  have := certificate1280
  rw [h.1] at this
  norm_num at this
def C1281 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1281 : C1281.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1281 : ¬ (C1281.det = 0 ∧ ∀ i, C1281.adjugate i i ≠ 0) := by
  intro h
  have := certificate1281
  rw [h.1] at this
  norm_num at this
def C1282 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1282 : C1282.det = (-54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1282 : ¬ (C1282.det = 0 ∧ ∀ i, C1282.adjugate i i ≠ 0) := by
  intro h
  have := certificate1282
  rw [h.1] at this
  norm_num at this
def C1283 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1283 : C1283.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1283 : ¬ (C1283.det = 0 ∧ ∀ i, C1283.adjugate i i ≠ 0) := by
  intro h
  have := certificate1283
  rw [h.1] at this
  norm_num at this
def C1284 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1284 : C1284.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1284 : ¬ (C1284.det = 0 ∧ ∀ i, C1284.adjugate i i ≠ 0) := by
  intro h
  have := certificate1284
  rw [h.1] at this
  norm_num at this
def C1285 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1285 : C1285.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1285 : ¬ (C1285.det = 0 ∧ ∀ i, C1285.adjugate i i ≠ 0) := by
  intro h
  have := certificate1285
  rw [h.1] at this
  norm_num at this
def C1286 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1286 : C1286.det = (76 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1286 : ¬ (C1286.det = 0 ∧ ∀ i, C1286.adjugate i i ≠ 0) := by
  intro h
  have := certificate1286
  rw [h.1] at this
  norm_num at this
def C1287 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1287 : C1287.det = (76 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1287 : ¬ (C1287.det = 0 ∧ ∀ i, C1287.adjugate i i ≠ 0) := by
  intro h
  have := certificate1287
  rw [h.1] at this
  norm_num at this
def C1288 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1288 : C1288.det = (76 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1288 : ¬ (C1288.det = 0 ∧ ∀ i, C1288.adjugate i i ≠ 0) := by
  intro h
  have := certificate1288
  rw [h.1] at this
  norm_num at this
def C1289 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1289 : C1289.det = (76 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1289 : ¬ (C1289.det = 0 ∧ ∀ i, C1289.adjugate i i ≠ 0) := by
  intro h
  have := certificate1289
  rw [h.1] at this
  norm_num at this
def C1290 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1290 : C1290.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1290 : ¬ (C1290.det = 0 ∧ ∀ i, C1290.adjugate i i ≠ 0) := by
  intro h
  have := certificate1290
  rw [h.1] at this
  norm_num at this
def C1291 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, -1, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1291 : C1291.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1291 : ¬ (C1291.det = 0 ∧ ∀ i, C1291.adjugate i i ≠ 0) := by
  intro h
  have := certificate1291
  rw [h.1] at this
  norm_num at this
def C1292 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1292 : C1292.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1292 : ¬ (C1292.det = 0 ∧ ∀ i, C1292.adjugate i i ≠ 0) := by
  intro h
  have := certificate1292
  rw [h.1] at this
  norm_num at this
def C1293 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1293 : C1293.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1293 : ¬ (C1293.det = 0 ∧ ∀ i, C1293.adjugate i i ≠ 0) := by
  intro h
  have := certificate1293
  rw [h.1] at this
  norm_num at this
def C1294 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1294 : C1294.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1294 : ¬ (C1294.det = 0 ∧ ∀ i, C1294.adjugate i i ≠ 0) := by
  intro h
  have := certificate1294
  rw [h.1] at this
  norm_num at this
def C1295 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1295 : C1295.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1295 : ¬ (C1295.det = 0 ∧ ∀ i, C1295.adjugate i i ≠ 0) := by
  intro h
  have := certificate1295
  rw [h.1] at this
  norm_num at this
def C1296 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1296 : C1296.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1296 : ¬ (C1296.det = 0 ∧ ∀ i, C1296.adjugate i i ≠ 0) := by
  intro h
  have := certificate1296
  rw [h.1] at this
  norm_num at this
def C1297 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1297 : C1297.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1297 : ¬ (C1297.det = 0 ∧ ∀ i, C1297.adjugate i i ≠ 0) := by
  intro h
  have := certificate1297
  rw [h.1] at this
  norm_num at this
def C1298 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1298 : C1298.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1298 : ¬ (C1298.det = 0 ∧ ∀ i, C1298.adjugate i i ≠ 0) := by
  intro h
  have := certificate1298
  rw [h.1] at this
  norm_num at this
def C1299 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1299 : C1299.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1299 : ¬ (C1299.det = 0 ∧ ∀ i, C1299.adjugate i i ≠ 0) := by
  intro h
  have := certificate1299
  rw [h.1] at this
  norm_num at this
def C1300 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1300 : C1300.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1300 : ¬ (C1300.det = 0 ∧ ∀ i, C1300.adjugate i i ≠ 0) := by
  intro h
  have := certificate1300
  rw [h.1] at this
  norm_num at this
def C1301 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1301 : C1301.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1301 : ¬ (C1301.det = 0 ∧ ∀ i, C1301.adjugate i i ≠ 0) := by
  intro h
  have := certificate1301
  rw [h.1] at this
  norm_num at this
def C1302 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1302 : C1302.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1302 : ¬ (C1302.det = 0 ∧ ∀ i, C1302.adjugate i i ≠ 0) := by
  intro h
  have := certificate1302
  rw [h.1] at this
  norm_num at this
def C1303 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1303 : C1303.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1303 : ¬ (C1303.det = 0 ∧ ∀ i, C1303.adjugate i i ≠ 0) := by
  intro h
  have := certificate1303
  rw [h.1] at this
  norm_num at this
def C1304 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1304 : C1304.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1304 : ¬ (C1304.det = 0 ∧ ∀ i, C1304.adjugate i i ≠ 0) := by
  intro h
  have := certificate1304
  rw [h.1] at this
  norm_num at this
def C1305 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1305 : C1305.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1305 : ¬ (C1305.det = 0 ∧ ∀ i, C1305.adjugate i i ≠ 0) := by
  intro h
  have := certificate1305
  rw [h.1] at this
  norm_num at this
def C1306 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1306 : C1306.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1306 : ¬ (C1306.det = 0 ∧ ∀ i, C1306.adjugate i i ≠ 0) := by
  intro h
  have := certificate1306
  rw [h.1] at this
  norm_num at this
def C1307 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1307 : C1307.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1307 : ¬ (C1307.det = 0 ∧ ∀ i, C1307.adjugate i i ≠ 0) := by
  intro h
  have := certificate1307
  rw [h.1] at this
  norm_num at this
def C1308 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1308 : C1308.det = (49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1308 : ¬ (C1308.det = 0 ∧ ∀ i, C1308.adjugate i i ≠ 0) := by
  intro h
  have := certificate1308
  rw [h.1] at this
  norm_num at this
def C1309 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1309 : C1309.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1309 : ¬ (C1309.det = 0 ∧ ∀ i, C1309.adjugate i i ≠ 0) := by
  intro h
  have := certificate1309
  rw [h.1] at this
  norm_num at this
def C1310 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1310 : C1310.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1310 : ¬ (C1310.det = 0 ∧ ∀ i, C1310.adjugate i i ≠ 0) := by
  intro h
  have := certificate1310
  rw [h.1] at this
  norm_num at this
def C1311 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1311 : C1311.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1311 : ¬ (C1311.det = 0 ∧ ∀ i, C1311.adjugate i i ≠ 0) := by
  intro h
  have := certificate1311
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0040
