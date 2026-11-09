import VerifiedDet
namespace Nut8.NewCertificates0196
def C6272 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6272 : C6272.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6272 : ¬ (C6272.det = 0 ∧ ∀ i, C6272.adjugate i i ≠ 0) := by
  intro h
  have := certificate6272
  rw [h.1] at this
  norm_num at this
def C6273 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6273 : C6273.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6273 : ¬ (C6273.det = 0 ∧ ∀ i, C6273.adjugate i i ≠ 0) := by
  intro h
  have := certificate6273
  rw [h.1] at this
  norm_num at this
def C6274 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6274 : C6274.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6274 : ¬ (C6274.det = 0 ∧ ∀ i, C6274.adjugate i i ≠ 0) := by
  intro h
  have := certificate6274
  rw [h.1] at this
  norm_num at this
def C6275 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6275 : C6275.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6275 : ¬ (C6275.det = 0 ∧ ∀ i, C6275.adjugate i i ≠ 0) := by
  intro h
  have := certificate6275
  rw [h.1] at this
  norm_num at this
def C6276 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6276 : C6276.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6276 : ¬ (C6276.det = 0 ∧ ∀ i, C6276.adjugate i i ≠ 0) := by
  intro h
  have := certificate6276
  rw [h.1] at this
  norm_num at this
def C6277 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6277 : C6277.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6277 : ¬ (C6277.det = 0 ∧ ∀ i, C6277.adjugate i i ≠ 0) := by
  intro h
  have := certificate6277
  rw [h.1] at this
  norm_num at this
def C6278 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6278 : C6278.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6278 : ¬ (C6278.det = 0 ∧ ∀ i, C6278.adjugate i i ≠ 0) := by
  intro h
  have := certificate6278
  rw [h.1] at this
  norm_num at this
def C6279 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6279 : C6279.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6279 : ¬ (C6279.det = 0 ∧ ∀ i, C6279.adjugate i i ≠ 0) := by
  intro h
  have := certificate6279
  rw [h.1] at this
  norm_num at this
def C6280 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6280 : C6280.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6280 : ¬ (C6280.det = 0 ∧ ∀ i, C6280.adjugate i i ≠ 0) := by
  intro h
  have := certificate6280
  rw [h.1] at this
  norm_num at this
def C6281 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6281 : C6281.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6281 : ¬ (C6281.det = 0 ∧ ∀ i, C6281.adjugate i i ≠ 0) := by
  intro h
  have := certificate6281
  rw [h.1] at this
  norm_num at this
def C6282 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6282 : C6282.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6282 : ¬ (C6282.det = 0 ∧ ∀ i, C6282.adjugate i i ≠ 0) := by
  intro h
  have := certificate6282
  rw [h.1] at this
  norm_num at this
def C6283 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6283 : C6283.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6283 : ¬ (C6283.det = 0 ∧ ∀ i, C6283.adjugate i i ≠ 0) := by
  intro h
  have := certificate6283
  rw [h.1] at this
  norm_num at this
def C6284 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6284 : C6284.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6284 : ¬ (C6284.det = 0 ∧ ∀ i, C6284.adjugate i i ≠ 0) := by
  intro h
  have := certificate6284
  rw [h.1] at this
  norm_num at this
def C6285 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6285 : C6285.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6285 : ¬ (C6285.det = 0 ∧ ∀ i, C6285.adjugate i i ≠ 0) := by
  intro h
  have := certificate6285
  rw [h.1] at this
  norm_num at this
def C6286 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6286 : C6286.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6286 : ¬ (C6286.det = 0 ∧ ∀ i, C6286.adjugate i i ≠ 0) := by
  intro h
  have := certificate6286
  rw [h.1] at this
  norm_num at this
def C6287 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6287 : C6287.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6287 : ¬ (C6287.det = 0 ∧ ∀ i, C6287.adjugate i i ≠ 0) := by
  intro h
  have := certificate6287
  rw [h.1] at this
  norm_num at this
def C6288 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6288 : C6288.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6288 : ¬ (C6288.det = 0 ∧ ∀ i, C6288.adjugate i i ≠ 0) := by
  intro h
  have := certificate6288
  rw [h.1] at this
  norm_num at this
def C6289 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6289 : C6289.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6289 : ¬ (C6289.det = 0 ∧ ∀ i, C6289.adjugate i i ≠ 0) := by
  intro h
  have := certificate6289
  rw [h.1] at this
  norm_num at this
def C6290 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6290 : C6290.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6290 : ¬ (C6290.det = 0 ∧ ∀ i, C6290.adjugate i i ≠ 0) := by
  intro h
  have := certificate6290
  rw [h.1] at this
  norm_num at this
def C6291 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6291 : C6291.det = (-27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6291 : ¬ (C6291.det = 0 ∧ ∀ i, C6291.adjugate i i ≠ 0) := by
  intro h
  have := certificate6291
  rw [h.1] at this
  norm_num at this
def C6292 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6292 : C6292.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6292 : ¬ (C6292.det = 0 ∧ ∀ i, C6292.adjugate i i ≠ 0) := by
  intro h
  have := certificate6292
  rw [h.1] at this
  norm_num at this
def C6293 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6293 : C6293.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6293 : ¬ (C6293.det = 0 ∧ ∀ i, C6293.adjugate i i ≠ 0) := by
  intro h
  have := certificate6293
  rw [h.1] at this
  norm_num at this
def C6294 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6294 : C6294.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6294 : ¬ (C6294.det = 0 ∧ ∀ i, C6294.adjugate i i ≠ 0) := by
  intro h
  have := certificate6294
  rw [h.1] at this
  norm_num at this
def C6295 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6295 : C6295.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6295 : ¬ (C6295.det = 0 ∧ ∀ i, C6295.adjugate i i ≠ 0) := by
  intro h
  have := certificate6295
  rw [h.1] at this
  norm_num at this
def C6296 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6296 : C6296.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6296 : ¬ (C6296.det = 0 ∧ ∀ i, C6296.adjugate i i ≠ 0) := by
  intro h
  have := certificate6296
  rw [h.1] at this
  norm_num at this
def C6297 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6297 : C6297.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6297 : ¬ (C6297.det = 0 ∧ ∀ i, C6297.adjugate i i ≠ 0) := by
  intro h
  have := certificate6297
  rw [h.1] at this
  norm_num at this
def C6298 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6298 : C6298.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6298 : ¬ (C6298.det = 0 ∧ ∀ i, C6298.adjugate i i ≠ 0) := by
  intro h
  have := certificate6298
  rw [h.1] at this
  norm_num at this
def C6299 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6299 : C6299.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6299 : ¬ (C6299.det = 0 ∧ ∀ i, C6299.adjugate i i ≠ 0) := by
  intro h
  have := certificate6299
  rw [h.1] at this
  norm_num at this
def C6300 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6300 : C6300.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6300 : ¬ (C6300.det = 0 ∧ ∀ i, C6300.adjugate i i ≠ 0) := by
  intro h
  have := certificate6300
  rw [h.1] at this
  norm_num at this
def C6301 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6301 : C6301.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6301 : ¬ (C6301.det = 0 ∧ ∀ i, C6301.adjugate i i ≠ 0) := by
  intro h
  have := certificate6301
  rw [h.1] at this
  norm_num at this
def C6302 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6302 : C6302.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6302 : ¬ (C6302.det = 0 ∧ ∀ i, C6302.adjugate i i ≠ 0) := by
  intro h
  have := certificate6302
  rw [h.1] at this
  norm_num at this
def C6303 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6303 : C6303.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6303 : ¬ (C6303.det = 0 ∧ ∀ i, C6303.adjugate i i ≠ 0) := by
  intro h
  have := certificate6303
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0196
