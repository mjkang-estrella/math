import VerifiedDet
namespace Nut8.NewCertificates0103
def C3296 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3296 : C3296.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3296 : ¬ (C3296.det = 0 ∧ ∀ i, C3296.adjugate i i ≠ 0) := by
  intro h
  have := certificate3296
  rw [h.1] at this
  norm_num at this
def C3297 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3297 : C3297.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3297 : ¬ (C3297.det = 0 ∧ ∀ i, C3297.adjugate i i ≠ 0) := by
  intro h
  have := certificate3297
  rw [h.1] at this
  norm_num at this
def C3298 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3298 : C3298.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3298 : ¬ (C3298.det = 0 ∧ ∀ i, C3298.adjugate i i ≠ 0) := by
  intro h
  have := certificate3298
  rw [h.1] at this
  norm_num at this
def C3299 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3299 : C3299.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3299 : ¬ (C3299.det = 0 ∧ ∀ i, C3299.adjugate i i ≠ 0) := by
  intro h
  have := certificate3299
  rw [h.1] at this
  norm_num at this
def C3300 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3300 : C3300.det = (30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3300 : ¬ (C3300.det = 0 ∧ ∀ i, C3300.adjugate i i ≠ 0) := by
  intro h
  have := certificate3300
  rw [h.1] at this
  norm_num at this
def C3301 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3301 : C3301.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3301 : ¬ (C3301.det = 0 ∧ ∀ i, C3301.adjugate i i ≠ 0) := by
  intro h
  have := certificate3301
  rw [h.1] at this
  norm_num at this
def C3302 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3302 : C3302.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3302 : ¬ (C3302.det = 0 ∧ ∀ i, C3302.adjugate i i ≠ 0) := by
  intro h
  have := certificate3302
  rw [h.1] at this
  norm_num at this
def C3303 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3303 : C3303.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3303 : ¬ (C3303.det = 0 ∧ ∀ i, C3303.adjugate i i ≠ 0) := by
  intro h
  have := certificate3303
  rw [h.1] at this
  norm_num at this
def C3304 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3304 : C3304.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3304 : ¬ (C3304.det = 0 ∧ ∀ i, C3304.adjugate i i ≠ 0) := by
  intro h
  have := certificate3304
  rw [h.1] at this
  norm_num at this
def C3305 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3305 : C3305.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3305 : ¬ (C3305.det = 0 ∧ ∀ i, C3305.adjugate i i ≠ 0) := by
  intro h
  have := certificate3305
  rw [h.1] at this
  norm_num at this
def C3306 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3306 : C3306.det = (-74 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3306 : ¬ (C3306.det = 0 ∧ ∀ i, C3306.adjugate i i ≠ 0) := by
  intro h
  have := certificate3306
  rw [h.1] at this
  norm_num at this
def C3307 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3307 : C3307.det = (106 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3307 : ¬ (C3307.det = 0 ∧ ∀ i, C3307.adjugate i i ≠ 0) := by
  intro h
  have := certificate3307
  rw [h.1] at this
  norm_num at this
def C3308 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3308 : C3308.det = (106 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3308 : ¬ (C3308.det = 0 ∧ ∀ i, C3308.adjugate i i ≠ 0) := by
  intro h
  have := certificate3308
  rw [h.1] at this
  norm_num at this
def C3309 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3309 : C3309.det = (-74 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3309 : ¬ (C3309.det = 0 ∧ ∀ i, C3309.adjugate i i ≠ 0) := by
  intro h
  have := certificate3309
  rw [h.1] at this
  norm_num at this
def C3310 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3310 : C3310.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3310 : ¬ (C3310.det = 0 ∧ ∀ i, C3310.adjugate i i ≠ 0) := by
  intro h
  have := certificate3310
  rw [h.1] at this
  norm_num at this
def C3311 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3311 : C3311.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3311 : ¬ (C3311.det = 0 ∧ ∀ i, C3311.adjugate i i ≠ 0) := by
  intro h
  have := certificate3311
  rw [h.1] at this
  norm_num at this
def C3312 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3312 : C3312.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3312 : ¬ (C3312.det = 0 ∧ ∀ i, C3312.adjugate i i ≠ 0) := by
  intro h
  have := certificate3312
  rw [h.1] at this
  norm_num at this
def C3313 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3313 : C3313.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3313 : ¬ (C3313.det = 0 ∧ ∀ i, C3313.adjugate i i ≠ 0) := by
  intro h
  have := certificate3313
  rw [h.1] at this
  norm_num at this
def C3314 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3314 : C3314.det = (-140 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3314 : ¬ (C3314.det = 0 ∧ ∀ i, C3314.adjugate i i ≠ 0) := by
  intro h
  have := certificate3314
  rw [h.1] at this
  norm_num at this
def C3315 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3315 : C3315.det = (148 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3315 : ¬ (C3315.det = 0 ∧ ∀ i, C3315.adjugate i i ≠ 0) := by
  intro h
  have := certificate3315
  rw [h.1] at this
  norm_num at this
def C3316 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3316 : C3316.det = (148 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3316 : ¬ (C3316.det = 0 ∧ ∀ i, C3316.adjugate i i ≠ 0) := by
  intro h
  have := certificate3316
  rw [h.1] at this
  norm_num at this
def C3317 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3317 : C3317.det = (-140 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3317 : ¬ (C3317.det = 0 ∧ ∀ i, C3317.adjugate i i ≠ 0) := by
  intro h
  have := certificate3317
  rw [h.1] at this
  norm_num at this
def C3318 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3318 : C3318.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3318 : ¬ (C3318.det = 0 ∧ ∀ i, C3318.adjugate i i ≠ 0) := by
  intro h
  have := certificate3318
  rw [h.1] at this
  norm_num at this
def C3319 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3319 : C3319.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3319 : ¬ (C3319.det = 0 ∧ ∀ i, C3319.adjugate i i ≠ 0) := by
  intro h
  have := certificate3319
  rw [h.1] at this
  norm_num at this
def C3320 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3320 : C3320.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3320 : ¬ (C3320.det = 0 ∧ ∀ i, C3320.adjugate i i ≠ 0) := by
  intro h
  have := certificate3320
  rw [h.1] at this
  norm_num at this
def C3321 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3321 : C3321.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3321 : ¬ (C3321.det = 0 ∧ ∀ i, C3321.adjugate i i ≠ 0) := by
  intro h
  have := certificate3321
  rw [h.1] at this
  norm_num at this
def C3322 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3322 : C3322.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3322 : ¬ (C3322.det = 0 ∧ ∀ i, C3322.adjugate i i ≠ 0) := by
  intro h
  have := certificate3322
  rw [h.1] at this
  norm_num at this
def C3323 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3323 : C3323.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3323 : ¬ (C3323.det = 0 ∧ ∀ i, C3323.adjugate i i ≠ 0) := by
  intro h
  have := certificate3323
  rw [h.1] at this
  norm_num at this
def C3324 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3324 : C3324.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3324 : ¬ (C3324.det = 0 ∧ ∀ i, C3324.adjugate i i ≠ 0) := by
  intro h
  have := certificate3324
  rw [h.1] at this
  norm_num at this
def C3325 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3325 : C3325.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3325 : ¬ (C3325.det = 0 ∧ ∀ i, C3325.adjugate i i ≠ 0) := by
  intro h
  have := certificate3325
  rw [h.1] at this
  norm_num at this
def C3326 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3326 : C3326.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3326 : ¬ (C3326.det = 0 ∧ ∀ i, C3326.adjugate i i ≠ 0) := by
  intro h
  have := certificate3326
  rw [h.1] at this
  norm_num at this
def C3327 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3327 : C3327.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3327 : ¬ (C3327.det = 0 ∧ ∀ i, C3327.adjugate i i ≠ 0) := by
  intro h
  have := certificate3327
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0103
