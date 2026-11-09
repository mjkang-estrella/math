import VerifiedDet
namespace Nut8.NewCertificates0226
def C7232 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7232 : C7232.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7232 : ¬ (C7232.det = 0 ∧ ∀ i, C7232.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7232
def C7233 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7233 : C7233.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7233 : ¬ (C7233.det = 0 ∧ ∀ i, C7233.adjugate i i ≠ 0) := by
  intro h
  have := certificate7233
  rw [h.1] at this
  norm_num at this
def C7234 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7234 : C7234.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7234 : ¬ (C7234.det = 0 ∧ ∀ i, C7234.adjugate i i ≠ 0) := by
  intro h
  have := certificate7234
  rw [h.1] at this
  norm_num at this
def C7235 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7235 : C7235.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7235 : ¬ (C7235.det = 0 ∧ ∀ i, C7235.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7235
def C7236 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7236 : C7236.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7236 : ¬ (C7236.det = 0 ∧ ∀ i, C7236.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7236
def C7237 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7237 : C7237.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7237 : ¬ (C7237.det = 0 ∧ ∀ i, C7237.adjugate i i ≠ 0) := by
  intro h
  have := certificate7237
  rw [h.1] at this
  norm_num at this
def C7238 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7238 : C7238.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7238 : ¬ (C7238.det = 0 ∧ ∀ i, C7238.adjugate i i ≠ 0) := by
  intro h
  have := certificate7238
  rw [h.1] at this
  norm_num at this
def C7239 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7239 : C7239.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7239 : ¬ (C7239.det = 0 ∧ ∀ i, C7239.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7239
def C7240 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7240 : C7240.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7240 : ¬ (C7240.det = 0 ∧ ∀ i, C7240.adjugate i i ≠ 0) := by
  intro h
  have := certificate7240
  rw [h.1] at this
  norm_num at this
def C7241 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7241 : C7241.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7241 : ¬ (C7241.det = 0 ∧ ∀ i, C7241.adjugate i i ≠ 0) := by
  intro h
  have := certificate7241
  rw [h.1] at this
  norm_num at this
def C7242 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7242 : C7242.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7242 : ¬ (C7242.det = 0 ∧ ∀ i, C7242.adjugate i i ≠ 0) := by
  intro h
  have := certificate7242
  rw [h.1] at this
  norm_num at this
def C7243 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7243 : C7243.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7243 : ¬ (C7243.det = 0 ∧ ∀ i, C7243.adjugate i i ≠ 0) := by
  intro h
  have := certificate7243
  rw [h.1] at this
  norm_num at this
def C7244 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7244 : C7244.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7244 : ¬ (C7244.det = 0 ∧ ∀ i, C7244.adjugate i i ≠ 0) := by
  intro h
  have := certificate7244
  rw [h.1] at this
  norm_num at this
def C7245 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7245 : C7245.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7245 : ¬ (C7245.det = 0 ∧ ∀ i, C7245.adjugate i i ≠ 0) := by
  intro h
  have := certificate7245
  rw [h.1] at this
  norm_num at this
def C7246 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7246 : C7246.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7246 : ¬ (C7246.det = 0 ∧ ∀ i, C7246.adjugate i i ≠ 0) := by
  intro h
  have := certificate7246
  rw [h.1] at this
  norm_num at this
def C7247 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7247 : C7247.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7247 : ¬ (C7247.det = 0 ∧ ∀ i, C7247.adjugate i i ≠ 0) := by
  intro h
  have := certificate7247
  rw [h.1] at this
  norm_num at this
def C7248 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7248 : C7248.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7248 : ¬ (C7248.det = 0 ∧ ∀ i, C7248.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7248
def C7249 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7249 : C7249.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7249 : ¬ (C7249.det = 0 ∧ ∀ i, C7249.adjugate i i ≠ 0) := by
  intro h
  have := certificate7249
  rw [h.1] at this
  norm_num at this
def C7250 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7250 : C7250.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7250 : ¬ (C7250.det = 0 ∧ ∀ i, C7250.adjugate i i ≠ 0) := by
  intro h
  have := certificate7250
  rw [h.1] at this
  norm_num at this
def C7251 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7251 : C7251.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7251 : ¬ (C7251.det = 0 ∧ ∀ i, C7251.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7251
def C7252 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7252 : C7252.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7252 : ¬ (C7252.det = 0 ∧ ∀ i, C7252.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7252
def C7253 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7253 : C7253.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7253 : ¬ (C7253.det = 0 ∧ ∀ i, C7253.adjugate i i ≠ 0) := by
  intro h
  have := certificate7253
  rw [h.1] at this
  norm_num at this
def C7254 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7254 : C7254.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7254 : ¬ (C7254.det = 0 ∧ ∀ i, C7254.adjugate i i ≠ 0) := by
  intro h
  have := certificate7254
  rw [h.1] at this
  norm_num at this
def C7255 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7255 : C7255.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7255 : ¬ (C7255.det = 0 ∧ ∀ i, C7255.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7255
def C7256 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7256 : C7256.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7256 : ¬ (C7256.det = 0 ∧ ∀ i, C7256.adjugate i i ≠ 0) := by
  intro h
  have := certificate7256
  rw [h.1] at this
  norm_num at this
def C7257 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7257 : C7257.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7257 : ¬ (C7257.det = 0 ∧ ∀ i, C7257.adjugate i i ≠ 0) := by
  intro h
  have := certificate7257
  rw [h.1] at this
  norm_num at this
def C7258 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7258 : C7258.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7258 : ¬ (C7258.det = 0 ∧ ∀ i, C7258.adjugate i i ≠ 0) := by
  intro h
  have := certificate7258
  rw [h.1] at this
  norm_num at this
def C7259 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7259 : C7259.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7259 : ¬ (C7259.det = 0 ∧ ∀ i, C7259.adjugate i i ≠ 0) := by
  intro h
  have := certificate7259
  rw [h.1] at this
  norm_num at this
def C7260 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7260 : C7260.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7260 : ¬ (C7260.det = 0 ∧ ∀ i, C7260.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7260
def C7261 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7261 : C7261.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7261 : ¬ (C7261.det = 0 ∧ ∀ i, C7261.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7261
def C7262 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7262 : C7262.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7262 : ¬ (C7262.det = 0 ∧ ∀ i, C7262.adjugate i i ≠ 0) := by
  intro h
  have := certificate7262
  rw [h.1] at this
  norm_num at this
def C7263 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7263 : C7263.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7263 : ¬ (C7263.det = 0 ∧ ∀ i, C7263.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7263
end Nut8.NewCertificates0226
