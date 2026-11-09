import VerifiedDet
namespace Nut8.NewCertificates0041
def C1312 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1312 : C1312.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1312 : ¬ (C1312.det = 0 ∧ ∀ i, C1312.adjugate i i ≠ 0) := by
  intro h
  have := certificate1312
  rw [h.1] at this
  norm_num at this
def C1313 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1313 : C1313.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1313 : ¬ (C1313.det = 0 ∧ ∀ i, C1313.adjugate i i ≠ 0) := by
  intro h
  have := certificate1313
  rw [h.1] at this
  norm_num at this
def C1314 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1314 : C1314.det = (81 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1314 : ¬ (C1314.det = 0 ∧ ∀ i, C1314.adjugate i i ≠ 0) := by
  intro h
  have := certificate1314
  rw [h.1] at this
  norm_num at this
def C1315 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1315 : C1315.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1315 : ¬ (C1315.det = 0 ∧ ∀ i, C1315.adjugate i i ≠ 0) := by
  intro h
  have := certificate1315
  rw [h.1] at this
  norm_num at this
def C1316 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1316 : C1316.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1316 : ¬ (C1316.det = 0 ∧ ∀ i, C1316.adjugate i i ≠ 0) := by
  intro h
  have := certificate1316
  rw [h.1] at this
  norm_num at this
def C1317 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1317 : C1317.det = (81 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1317 : ¬ (C1317.det = 0 ∧ ∀ i, C1317.adjugate i i ≠ 0) := by
  intro h
  have := certificate1317
  rw [h.1] at this
  norm_num at this
def C1318 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1318 : C1318.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1318 : ¬ (C1318.det = 0 ∧ ∀ i, C1318.adjugate i i ≠ 0) := by
  intro h
  have := certificate1318
  rw [h.1] at this
  norm_num at this
def C1319 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1319 : C1319.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1319 : ¬ (C1319.det = 0 ∧ ∀ i, C1319.adjugate i i ≠ 0) := by
  intro h
  have := certificate1319
  rw [h.1] at this
  norm_num at this
def C1320 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1320 : C1320.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1320 : ¬ (C1320.det = 0 ∧ ∀ i, C1320.adjugate i i ≠ 0) := by
  intro h
  have := certificate1320
  rw [h.1] at this
  norm_num at this
def C1321 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1321 : C1321.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1321 : ¬ (C1321.det = 0 ∧ ∀ i, C1321.adjugate i i ≠ 0) := by
  intro h
  have := certificate1321
  rw [h.1] at this
  norm_num at this
def C1322 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1322 : C1322.det = (-63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1322 : ¬ (C1322.det = 0 ∧ ∀ i, C1322.adjugate i i ≠ 0) := by
  intro h
  have := certificate1322
  rw [h.1] at this
  norm_num at this
def C1323 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1323 : C1323.det = (49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1323 : ¬ (C1323.det = 0 ∧ ∀ i, C1323.adjugate i i ≠ 0) := by
  intro h
  have := certificate1323
  rw [h.1] at this
  norm_num at this
def C1324 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1324 : C1324.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1324 : ¬ (C1324.det = 0 ∧ ∀ i, C1324.adjugate i i ≠ 0) := by
  intro h
  have := certificate1324
  rw [h.1] at this
  norm_num at this
def C1325 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1325 : C1325.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1325 : ¬ (C1325.det = 0 ∧ ∀ i, C1325.adjugate i i ≠ 0) := by
  intro h
  have := certificate1325
  rw [h.1] at this
  norm_num at this
def C1326 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1326 : C1326.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1326 : ¬ (C1326.det = 0 ∧ ∀ i, C1326.adjugate i i ≠ 0) := by
  intro h
  have := certificate1326
  rw [h.1] at this
  norm_num at this
def C1327 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1327 : C1327.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1327 : ¬ (C1327.det = 0 ∧ ∀ i, C1327.adjugate i i ≠ 0) := by
  intro h
  have := certificate1327
  rw [h.1] at this
  norm_num at this
def C1328 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1328 : C1328.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1328 : ¬ (C1328.det = 0 ∧ ∀ i, C1328.adjugate i i ≠ 0) := by
  intro h
  have := certificate1328
  rw [h.1] at this
  norm_num at this
def C1329 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1329 : C1329.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1329 : ¬ (C1329.det = 0 ∧ ∀ i, C1329.adjugate i i ≠ 0) := by
  intro h
  have := certificate1329
  rw [h.1] at this
  norm_num at this
def C1330 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1330 : C1330.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1330 : ¬ (C1330.det = 0 ∧ ∀ i, C1330.adjugate i i ≠ 0) := by
  intro h
  have := certificate1330
  rw [h.1] at this
  norm_num at this
def C1331 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1331 : C1331.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1331 : ¬ (C1331.det = 0 ∧ ∀ i, C1331.adjugate i i ≠ 0) := by
  intro h
  have := certificate1331
  rw [h.1] at this
  norm_num at this
def C1332 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1332 : C1332.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1332 : ¬ (C1332.det = 0 ∧ ∀ i, C1332.adjugate i i ≠ 0) := by
  intro h
  have := certificate1332
  rw [h.1] at this
  norm_num at this
def C1333 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1333 : C1333.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1333 : ¬ (C1333.det = 0 ∧ ∀ i, C1333.adjugate i i ≠ 0) := by
  intro h
  have := certificate1333
  rw [h.1] at this
  norm_num at this
def C1334 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1334 : C1334.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1334 : ¬ (C1334.det = 0 ∧ ∀ i, C1334.adjugate i i ≠ 0) := by
  intro h
  have := certificate1334
  rw [h.1] at this
  norm_num at this
def C1335 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1335 : C1335.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1335 : ¬ (C1335.det = 0 ∧ ∀ i, C1335.adjugate i i ≠ 0) := by
  intro h
  have := certificate1335
  rw [h.1] at this
  norm_num at this
def C1336 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1336 : C1336.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1336 : ¬ (C1336.det = 0 ∧ ∀ i, C1336.adjugate i i ≠ 0) := by
  intro h
  have := certificate1336
  rw [h.1] at this
  norm_num at this
def C1337 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1337 : C1337.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1337 : ¬ (C1337.det = 0 ∧ ∀ i, C1337.adjugate i i ≠ 0) := by
  intro h
  have := certificate1337
  rw [h.1] at this
  norm_num at this
def C1338 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1338 : C1338.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1338 : ¬ (C1338.det = 0 ∧ ∀ i, C1338.adjugate i i ≠ 0) := by
  intro h
  have := certificate1338
  rw [h.1] at this
  norm_num at this
def C1339 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1339 : C1339.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1339 : ¬ (C1339.det = 0 ∧ ∀ i, C1339.adjugate i i ≠ 0) := by
  intro h
  have := certificate1339
  rw [h.1] at this
  norm_num at this
def C1340 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1340 : C1340.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1340 : ¬ (C1340.det = 0 ∧ ∀ i, C1340.adjugate i i ≠ 0) := by
  intro h
  have := certificate1340
  rw [h.1] at this
  norm_num at this
def C1341 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1341 : C1341.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1341 : ¬ (C1341.det = 0 ∧ ∀ i, C1341.adjugate i i ≠ 0) := by
  intro h
  have := certificate1341
  rw [h.1] at this
  norm_num at this
def C1342 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1342 : C1342.det = (-37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1342 : ¬ (C1342.det = 0 ∧ ∀ i, C1342.adjugate i i ≠ 0) := by
  intro h
  have := certificate1342
  rw [h.1] at this
  norm_num at this
def C1343 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1343 : C1343.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1343 : ¬ (C1343.det = 0 ∧ ∀ i, C1343.adjugate i i ≠ 0) := by
  intro h
  have := certificate1343
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0041
