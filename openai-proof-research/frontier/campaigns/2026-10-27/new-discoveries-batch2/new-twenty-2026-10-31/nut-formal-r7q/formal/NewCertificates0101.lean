import VerifiedDet
namespace Nut8.NewCertificates0101
def C3232 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3232 : C3232.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3232 : ¬ (C3232.det = 0 ∧ ∀ i, C3232.adjugate i i ≠ 0) := by
  intro h
  have := certificate3232
  rw [h.1] at this
  norm_num at this
def C3233 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3233 : C3233.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3233 : ¬ (C3233.det = 0 ∧ ∀ i, C3233.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3233
def C3234 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3234 : C3234.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3234 : ¬ (C3234.det = 0 ∧ ∀ i, C3234.adjugate i i ≠ 0) := by
  intro h
  have := certificate3234
  rw [h.1] at this
  norm_num at this
def C3235 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3235 : C3235.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3235 : ¬ (C3235.det = 0 ∧ ∀ i, C3235.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3235
def C3236 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3236 : C3236.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3236 : ¬ (C3236.det = 0 ∧ ∀ i, C3236.adjugate i i ≠ 0) := by
  intro h
  have := certificate3236
  rw [h.1] at this
  norm_num at this
def C3237 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3237 : C3237.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3237 : ¬ (C3237.det = 0 ∧ ∀ i, C3237.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3237
def C3238 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3238 : C3238.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3238 : ¬ (C3238.det = 0 ∧ ∀ i, C3238.adjugate i i ≠ 0) := by
  intro h
  have := certificate3238
  rw [h.1] at this
  norm_num at this
def C3239 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3239 : C3239.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3239 : ¬ (C3239.det = 0 ∧ ∀ i, C3239.adjugate i i ≠ 0) := by
  intro h
  have := certificate3239
  rw [h.1] at this
  norm_num at this
def C3240 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3240 : C3240.det = (88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3240 : ¬ (C3240.det = 0 ∧ ∀ i, C3240.adjugate i i ≠ 0) := by
  intro h
  have := certificate3240
  rw [h.1] at this
  norm_num at this
def C3241 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3241 : C3241.det = (-104 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3241 : ¬ (C3241.det = 0 ∧ ∀ i, C3241.adjugate i i ≠ 0) := by
  intro h
  have := certificate3241
  rw [h.1] at this
  norm_num at this
def C3242 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3242 : C3242.det = (-104 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3242 : ¬ (C3242.det = 0 ∧ ∀ i, C3242.adjugate i i ≠ 0) := by
  intro h
  have := certificate3242
  rw [h.1] at this
  norm_num at this
def C3243 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3243 : C3243.det = (88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3243 : ¬ (C3243.det = 0 ∧ ∀ i, C3243.adjugate i i ≠ 0) := by
  intro h
  have := certificate3243
  rw [h.1] at this
  norm_num at this
def C3244 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3244 : C3244.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3244 : ¬ (C3244.det = 0 ∧ ∀ i, C3244.adjugate i i ≠ 0) := by
  intro h
  have := certificate3244
  rw [h.1] at this
  norm_num at this
def C3245 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3245 : C3245.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3245 : ¬ (C3245.det = 0 ∧ ∀ i, C3245.adjugate i i ≠ 0) := by
  intro h
  have := certificate3245
  rw [h.1] at this
  norm_num at this
def C3246 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3246 : C3246.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3246 : ¬ (C3246.det = 0 ∧ ∀ i, C3246.adjugate i i ≠ 0) := by
  intro h
  have := certificate3246
  rw [h.1] at this
  norm_num at this
def C3247 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3247 : C3247.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3247 : ¬ (C3247.det = 0 ∧ ∀ i, C3247.adjugate i i ≠ 0) := by
  intro h
  have := certificate3247
  rw [h.1] at this
  norm_num at this
def C3248 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3248 : C3248.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3248 : ¬ (C3248.det = 0 ∧ ∀ i, C3248.adjugate i i ≠ 0) := by
  intro h
  have := certificate3248
  rw [h.1] at this
  norm_num at this
def C3249 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3249 : C3249.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3249 : ¬ (C3249.det = 0 ∧ ∀ i, C3249.adjugate i i ≠ 0) := by
  intro h
  have := certificate3249
  rw [h.1] at this
  norm_num at this
def C3250 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3250 : C3250.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3250 : ¬ (C3250.det = 0 ∧ ∀ i, C3250.adjugate i i ≠ 0) := by
  intro h
  have := certificate3250
  rw [h.1] at this
  norm_num at this
def C3251 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3251 : C3251.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3251 : ¬ (C3251.det = 0 ∧ ∀ i, C3251.adjugate i i ≠ 0) := by
  intro h
  have := certificate3251
  rw [h.1] at this
  norm_num at this
def C3252 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3252 : C3252.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3252 : ¬ (C3252.det = 0 ∧ ∀ i, C3252.adjugate i i ≠ 0) := by
  intro h
  have := certificate3252
  rw [h.1] at this
  norm_num at this
def C3253 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3253 : C3253.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3253 : ¬ (C3253.det = 0 ∧ ∀ i, C3253.adjugate i i ≠ 0) := by
  intro h
  have := certificate3253
  rw [h.1] at this
  norm_num at this
def C3254 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3254 : C3254.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3254 : ¬ (C3254.det = 0 ∧ ∀ i, C3254.adjugate i i ≠ 0) := by
  intro h
  have := certificate3254
  rw [h.1] at this
  norm_num at this
def C3255 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3255 : C3255.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3255 : ¬ (C3255.det = 0 ∧ ∀ i, C3255.adjugate i i ≠ 0) := by
  intro h
  have := certificate3255
  rw [h.1] at this
  norm_num at this
def C3256 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3256 : C3256.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3256 : ¬ (C3256.det = 0 ∧ ∀ i, C3256.adjugate i i ≠ 0) := by
  intro h
  have := certificate3256
  rw [h.1] at this
  norm_num at this
def C3257 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3257 : C3257.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3257 : ¬ (C3257.det = 0 ∧ ∀ i, C3257.adjugate i i ≠ 0) := by
  intro h
  have := certificate3257
  rw [h.1] at this
  norm_num at this
def C3258 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3258 : C3258.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3258 : ¬ (C3258.det = 0 ∧ ∀ i, C3258.adjugate i i ≠ 0) := by
  intro h
  have := certificate3258
  rw [h.1] at this
  norm_num at this
def C3259 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3259 : C3259.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3259 : ¬ (C3259.det = 0 ∧ ∀ i, C3259.adjugate i i ≠ 0) := by
  intro h
  have := certificate3259
  rw [h.1] at this
  norm_num at this
def C3260 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3260 : C3260.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3260 : ¬ (C3260.det = 0 ∧ ∀ i, C3260.adjugate i i ≠ 0) := by
  intro h
  have := certificate3260
  rw [h.1] at this
  norm_num at this
def C3261 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3261 : C3261.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3261 : ¬ (C3261.det = 0 ∧ ∀ i, C3261.adjugate i i ≠ 0) := by
  intro h
  have := certificate3261
  rw [h.1] at this
  norm_num at this
def C3262 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3262 : C3262.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3262 : ¬ (C3262.det = 0 ∧ ∀ i, C3262.adjugate i i ≠ 0) := by
  intro h
  have := certificate3262
  rw [h.1] at this
  norm_num at this
def C3263 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3263 : C3263.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3263 : ¬ (C3263.det = 0 ∧ ∀ i, C3263.adjugate i i ≠ 0) := by
  intro h
  have := certificate3263
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0101
