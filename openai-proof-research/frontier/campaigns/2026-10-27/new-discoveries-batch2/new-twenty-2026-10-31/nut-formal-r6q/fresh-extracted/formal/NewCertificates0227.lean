import VerifiedDet
namespace Nut8.NewCertificates0227
def C7264 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7264 : C7264.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7264 : ¬ (C7264.det = 0 ∧ ∀ i, C7264.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7264
def C7265 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7265 : C7265.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7265 : ¬ (C7265.det = 0 ∧ ∀ i, C7265.adjugate i i ≠ 0) := by
  intro h
  have := certificate7265
  rw [h.1] at this
  norm_num at this
def C7266 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7266 : C7266.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7266 : ¬ (C7266.det = 0 ∧ ∀ i, C7266.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7266
def C7267 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7267 : C7267.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7267 : ¬ (C7267.det = 0 ∧ ∀ i, C7267.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7267
def C7268 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7268 : C7268.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7268 : ¬ (C7268.det = 0 ∧ ∀ i, C7268.adjugate i i ≠ 0) := by
  intro h
  have := certificate7268
  rw [h.1] at this
  norm_num at this
def C7269 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7269 : C7269.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7269 : ¬ (C7269.det = 0 ∧ ∀ i, C7269.adjugate i i ≠ 0) := by
  intro h
  have := certificate7269
  rw [h.1] at this
  norm_num at this
def C7270 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7270 : C7270.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7270 : ¬ (C7270.det = 0 ∧ ∀ i, C7270.adjugate i i ≠ 0) := by
  intro h
  have := certificate7270
  rw [h.1] at this
  norm_num at this
def C7271 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7271 : C7271.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7271 : ¬ (C7271.det = 0 ∧ ∀ i, C7271.adjugate i i ≠ 0) := by
  intro h
  have := certificate7271
  rw [h.1] at this
  norm_num at this
def C7272 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7272 : C7272.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7272 : ¬ (C7272.det = 0 ∧ ∀ i, C7272.adjugate i i ≠ 0) := by
  intro h
  have := certificate7272
  rw [h.1] at this
  norm_num at this
def C7273 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7273 : C7273.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7273 : ¬ (C7273.det = 0 ∧ ∀ i, C7273.adjugate i i ≠ 0) := by
  intro h
  have := certificate7273
  rw [h.1] at this
  norm_num at this
def C7274 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7274 : C7274.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7274 : ¬ (C7274.det = 0 ∧ ∀ i, C7274.adjugate i i ≠ 0) := by
  intro h
  have := certificate7274
  rw [h.1] at this
  norm_num at this
def C7275 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7275 : C7275.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7275 : ¬ (C7275.det = 0 ∧ ∀ i, C7275.adjugate i i ≠ 0) := by
  intro h
  have := certificate7275
  rw [h.1] at this
  norm_num at this
def C7276 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7276 : C7276.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7276 : ¬ (C7276.det = 0 ∧ ∀ i, C7276.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7276
def C7277 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7277 : C7277.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7277 : ¬ (C7277.det = 0 ∧ ∀ i, C7277.adjugate i i ≠ 0) := by
  intro h
  have := certificate7277
  rw [h.1] at this
  norm_num at this
def C7278 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7278 : C7278.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7278 : ¬ (C7278.det = 0 ∧ ∀ i, C7278.adjugate i i ≠ 0) := by
  intro h
  have := certificate7278
  rw [h.1] at this
  norm_num at this
def C7279 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7279 : C7279.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7279 : ¬ (C7279.det = 0 ∧ ∀ i, C7279.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7279
def C7280 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7280 : C7280.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7280 : ¬ (C7280.det = 0 ∧ ∀ i, C7280.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7280
def C7281 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7281 : C7281.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7281 : ¬ (C7281.det = 0 ∧ ∀ i, C7281.adjugate i i ≠ 0) := by
  intro h
  have := certificate7281
  rw [h.1] at this
  norm_num at this
def C7282 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7282 : C7282.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7282 : ¬ (C7282.det = 0 ∧ ∀ i, C7282.adjugate i i ≠ 0) := by
  intro h
  have := certificate7282
  rw [h.1] at this
  norm_num at this
def C7283 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7283 : C7283.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7283 : ¬ (C7283.det = 0 ∧ ∀ i, C7283.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7283
def C7284 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7284 : C7284.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7284 : ¬ (C7284.det = 0 ∧ ∀ i, C7284.adjugate i i ≠ 0) := by
  intro h
  have := certificate7284
  rw [h.1] at this
  norm_num at this
def C7285 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7285 : C7285.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7285 : ¬ (C7285.det = 0 ∧ ∀ i, C7285.adjugate i i ≠ 0) := by
  intro h
  have := certificate7285
  rw [h.1] at this
  norm_num at this
def C7286 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7286 : C7286.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7286 : ¬ (C7286.det = 0 ∧ ∀ i, C7286.adjugate i i ≠ 0) := by
  intro h
  have := certificate7286
  rw [h.1] at this
  norm_num at this
def C7287 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7287 : C7287.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7287 : ¬ (C7287.det = 0 ∧ ∀ i, C7287.adjugate i i ≠ 0) := by
  intro h
  have := certificate7287
  rw [h.1] at this
  norm_num at this
def C7288 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7288 : C7288.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7288 : ¬ (C7288.det = 0 ∧ ∀ i, C7288.adjugate i i ≠ 0) := by
  intro h
  have := certificate7288
  rw [h.1] at this
  norm_num at this
def C7289 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7289 : C7289.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7289 : ¬ (C7289.det = 0 ∧ ∀ i, C7289.adjugate i i ≠ 0) := by
  intro h
  have := certificate7289
  rw [h.1] at this
  norm_num at this
def C7290 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7290 : C7290.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7290 : ¬ (C7290.det = 0 ∧ ∀ i, C7290.adjugate i i ≠ 0) := by
  intro h
  have := certificate7290
  rw [h.1] at this
  norm_num at this
def C7291 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 0, 1, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7291 : C7291.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7291 : ¬ (C7291.det = 0 ∧ ∀ i, C7291.adjugate i i ≠ 0) := by
  intro h
  have := certificate7291
  rw [h.1] at this
  norm_num at this
def C7292 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7292 : C7292.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7292 : ¬ (C7292.det = 0 ∧ ∀ i, C7292.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7292
def C7293 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7293 : C7293.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7293 : ¬ (C7293.det = 0 ∧ ∀ i, C7293.adjugate i i ≠ 0) := by
  intro h
  have := certificate7293
  rw [h.1] at this
  norm_num at this
def C7294 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7294 : C7294.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7294 : ¬ (C7294.det = 0 ∧ ∀ i, C7294.adjugate i i ≠ 0) := by
  intro h
  have := certificate7294
  rw [h.1] at this
  norm_num at this
def C7295 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7295 : C7295.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7295 : ¬ (C7295.det = 0 ∧ ∀ i, C7295.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7295
end Nut8.NewCertificates0227
