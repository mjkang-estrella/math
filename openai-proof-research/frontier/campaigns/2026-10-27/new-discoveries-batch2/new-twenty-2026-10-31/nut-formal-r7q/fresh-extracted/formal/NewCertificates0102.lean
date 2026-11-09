import VerifiedDet
namespace Nut8.NewCertificates0102
def C3264 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3264 : C3264.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3264 : ¬ (C3264.det = 0 ∧ ∀ i, C3264.adjugate i i ≠ 0) := by
  intro h
  have := certificate3264
  rw [h.1] at this
  norm_num at this
def C3265 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3265 : C3265.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3265 : ¬ (C3265.det = 0 ∧ ∀ i, C3265.adjugate i i ≠ 0) := by
  intro h
  have := certificate3265
  rw [h.1] at this
  norm_num at this
def C3266 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3266 : C3266.det = (-43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3266 : ¬ (C3266.det = 0 ∧ ∀ i, C3266.adjugate i i ≠ 0) := by
  intro h
  have := certificate3266
  rw [h.1] at this
  norm_num at this
def C3267 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3267 : C3267.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3267 : ¬ (C3267.det = 0 ∧ ∀ i, C3267.adjugate i i ≠ 0) := by
  intro h
  have := certificate3267
  rw [h.1] at this
  norm_num at this
def C3268 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3268 : C3268.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3268 : ¬ (C3268.det = 0 ∧ ∀ i, C3268.adjugate i i ≠ 0) := by
  intro h
  have := certificate3268
  rw [h.1] at this
  norm_num at this
def C3269 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3269 : C3269.det = (-43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3269 : ¬ (C3269.det = 0 ∧ ∀ i, C3269.adjugate i i ≠ 0) := by
  intro h
  have := certificate3269
  rw [h.1] at this
  norm_num at this
def C3270 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3270 : C3270.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3270 : ¬ (C3270.det = 0 ∧ ∀ i, C3270.adjugate i i ≠ 0) := by
  intro h
  have := certificate3270
  rw [h.1] at this
  norm_num at this
def C3271 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3271 : C3271.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3271 : ¬ (C3271.det = 0 ∧ ∀ i, C3271.adjugate i i ≠ 0) := by
  intro h
  have := certificate3271
  rw [h.1] at this
  norm_num at this
def C3272 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3272 : C3272.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3272 : ¬ (C3272.det = 0 ∧ ∀ i, C3272.adjugate i i ≠ 0) := by
  intro h
  have := certificate3272
  rw [h.1] at this
  norm_num at this
def C3273 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3273 : C3273.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3273 : ¬ (C3273.det = 0 ∧ ∀ i, C3273.adjugate i i ≠ 0) := by
  intro h
  have := certificate3273
  rw [h.1] at this
  norm_num at this
def C3274 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3274 : C3274.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3274 : ¬ (C3274.det = 0 ∧ ∀ i, C3274.adjugate i i ≠ 0) := by
  intro h
  have := certificate3274
  rw [h.1] at this
  norm_num at this
def C3275 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3275 : C3275.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3275 : ¬ (C3275.det = 0 ∧ ∀ i, C3275.adjugate i i ≠ 0) := by
  intro h
  have := certificate3275
  rw [h.1] at this
  norm_num at this
def C3276 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3276 : C3276.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3276 : ¬ (C3276.det = 0 ∧ ∀ i, C3276.adjugate i i ≠ 0) := by
  intro h
  have := certificate3276
  rw [h.1] at this
  norm_num at this
def C3277 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3277 : C3277.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3277 : ¬ (C3277.det = 0 ∧ ∀ i, C3277.adjugate i i ≠ 0) := by
  intro h
  have := certificate3277
  rw [h.1] at this
  norm_num at this
def C3278 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3278 : C3278.det = (-58 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3278 : ¬ (C3278.det = 0 ∧ ∀ i, C3278.adjugate i i ≠ 0) := by
  intro h
  have := certificate3278
  rw [h.1] at this
  norm_num at this
def C3279 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3279 : C3279.det = (-38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3279 : ¬ (C3279.det = 0 ∧ ∀ i, C3279.adjugate i i ≠ 0) := by
  intro h
  have := certificate3279
  rw [h.1] at this
  norm_num at this
def C3280 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3280 : C3280.det = (54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3280 : ¬ (C3280.det = 0 ∧ ∀ i, C3280.adjugate i i ≠ 0) := by
  intro h
  have := certificate3280
  rw [h.1] at this
  norm_num at this
def C3281 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3281 : C3281.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3281 : ¬ (C3281.det = 0 ∧ ∀ i, C3281.adjugate i i ≠ 0) := by
  intro h
  have := certificate3281
  rw [h.1] at this
  norm_num at this
def C3282 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3282 : C3282.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3282 : ¬ (C3282.det = 0 ∧ ∀ i, C3282.adjugate i i ≠ 0) := by
  intro h
  have := certificate3282
  rw [h.1] at this
  norm_num at this
def C3283 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3283 : C3283.det = (54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3283 : ¬ (C3283.det = 0 ∧ ∀ i, C3283.adjugate i i ≠ 0) := by
  intro h
  have := certificate3283
  rw [h.1] at this
  norm_num at this
def C3284 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3284 : C3284.det = (-38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3284 : ¬ (C3284.det = 0 ∧ ∀ i, C3284.adjugate i i ≠ 0) := by
  intro h
  have := certificate3284
  rw [h.1] at this
  norm_num at this
def C3285 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3285 : C3285.det = (-58 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3285 : ¬ (C3285.det = 0 ∧ ∀ i, C3285.adjugate i i ≠ 0) := by
  intro h
  have := certificate3285
  rw [h.1] at this
  norm_num at this
def C3286 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3286 : C3286.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3286 : ¬ (C3286.det = 0 ∧ ∀ i, C3286.adjugate i i ≠ 0) := by
  intro h
  have := certificate3286
  rw [h.1] at this
  norm_num at this
def C3287 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3287 : C3287.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3287 : ¬ (C3287.det = 0 ∧ ∀ i, C3287.adjugate i i ≠ 0) := by
  intro h
  have := certificate3287
  rw [h.1] at this
  norm_num at this
def C3288 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3288 : C3288.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3288 : ¬ (C3288.det = 0 ∧ ∀ i, C3288.adjugate i i ≠ 0) := by
  intro h
  have := certificate3288
  rw [h.1] at this
  norm_num at this
def C3289 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3289 : C3289.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3289 : ¬ (C3289.det = 0 ∧ ∀ i, C3289.adjugate i i ≠ 0) := by
  intro h
  have := certificate3289
  rw [h.1] at this
  norm_num at this
def C3290 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3290 : C3290.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3290 : ¬ (C3290.det = 0 ∧ ∀ i, C3290.adjugate i i ≠ 0) := by
  intro h
  have := certificate3290
  rw [h.1] at this
  norm_num at this
def C3291 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3291 : C3291.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3291 : ¬ (C3291.det = 0 ∧ ∀ i, C3291.adjugate i i ≠ 0) := by
  intro h
  have := certificate3291
  rw [h.1] at this
  norm_num at this
def C3292 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3292 : C3292.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3292 : ¬ (C3292.det = 0 ∧ ∀ i, C3292.adjugate i i ≠ 0) := by
  intro h
  have := certificate3292
  rw [h.1] at this
  norm_num at this
def C3293 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3293 : C3293.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3293 : ¬ (C3293.det = 0 ∧ ∀ i, C3293.adjugate i i ≠ 0) := by
  intro h
  have := certificate3293
  rw [h.1] at this
  norm_num at this
def C3294 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3294 : C3294.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3294 : ¬ (C3294.det = 0 ∧ ∀ i, C3294.adjugate i i ≠ 0) := by
  intro h
  have := certificate3294
  rw [h.1] at this
  norm_num at this
def C3295 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3295 : C3295.det = (30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3295 : ¬ (C3295.det = 0 ∧ ∀ i, C3295.adjugate i i ≠ 0) := by
  intro h
  have := certificate3295
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0102
