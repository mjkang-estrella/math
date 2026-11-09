import VerifiedDet
namespace Nut8.NewCertificates0228
def C7296 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7296 : C7296.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7296 : ¬ (C7296.det = 0 ∧ ∀ i, C7296.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7296
def C7297 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7297 : C7297.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7297 : ¬ (C7297.det = 0 ∧ ∀ i, C7297.adjugate i i ≠ 0) := by
  intro h
  have := certificate7297
  rw [h.1] at this
  norm_num at this
def C7298 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7298 : C7298.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7298 : ¬ (C7298.det = 0 ∧ ∀ i, C7298.adjugate i i ≠ 0) := by
  intro h
  have := certificate7298
  rw [h.1] at this
  norm_num at this
def C7299 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7299 : C7299.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7299 : ¬ (C7299.det = 0 ∧ ∀ i, C7299.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7299
def C7300 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7300 : C7300.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7300 : ¬ (C7300.det = 0 ∧ ∀ i, C7300.adjugate i i ≠ 0) := by
  intro h
  have := certificate7300
  rw [h.1] at this
  norm_num at this
def C7301 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7301 : C7301.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7301 : ¬ (C7301.det = 0 ∧ ∀ i, C7301.adjugate i i ≠ 0) := by
  intro h
  have := certificate7301
  rw [h.1] at this
  norm_num at this
def C7302 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7302 : C7302.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7302 : ¬ (C7302.det = 0 ∧ ∀ i, C7302.adjugate i i ≠ 0) := by
  intro h
  have := certificate7302
  rw [h.1] at this
  norm_num at this
def C7303 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7303 : C7303.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7303 : ¬ (C7303.det = 0 ∧ ∀ i, C7303.adjugate i i ≠ 0) := by
  intro h
  have := certificate7303
  rw [h.1] at this
  norm_num at this
def C7304 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7304 : C7304.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7304 : ¬ (C7304.det = 0 ∧ ∀ i, C7304.adjugate i i ≠ 0) := by
  intro h
  have := certificate7304
  rw [h.1] at this
  norm_num at this
def C7305 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7305 : C7305.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7305 : ¬ (C7305.det = 0 ∧ ∀ i, C7305.adjugate i i ≠ 0) := by
  intro h
  have := certificate7305
  rw [h.1] at this
  norm_num at this
def C7306 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7306 : C7306.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7306 : ¬ (C7306.det = 0 ∧ ∀ i, C7306.adjugate i i ≠ 0) := by
  intro h
  have := certificate7306
  rw [h.1] at this
  norm_num at this
def C7307 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7307 : C7307.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7307 : ¬ (C7307.det = 0 ∧ ∀ i, C7307.adjugate i i ≠ 0) := by
  intro h
  have := certificate7307
  rw [h.1] at this
  norm_num at this
def C7308 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7308 : C7308.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7308 : ¬ (C7308.det = 0 ∧ ∀ i, C7308.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7308
def C7309 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7309 : C7309.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7309 : ¬ (C7309.det = 0 ∧ ∀ i, C7309.adjugate i i ≠ 0) := by
  intro h
  have := certificate7309
  rw [h.1] at this
  norm_num at this
def C7310 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7310 : C7310.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7310 : ¬ (C7310.det = 0 ∧ ∀ i, C7310.adjugate i i ≠ 0) := by
  intro h
  have := certificate7310
  rw [h.1] at this
  norm_num at this
def C7311 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7311 : C7311.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7311 : ¬ (C7311.det = 0 ∧ ∀ i, C7311.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7311
def C7312 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7312 : C7312.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7312 : ¬ (C7312.det = 0 ∧ ∀ i, C7312.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7312
def C7313 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7313 : C7313.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7313 : ¬ (C7313.det = 0 ∧ ∀ i, C7313.adjugate i i ≠ 0) := by
  intro h
  have := certificate7313
  rw [h.1] at this
  norm_num at this
def C7314 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7314 : C7314.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7314 : ¬ (C7314.det = 0 ∧ ∀ i, C7314.adjugate i i ≠ 0) := by
  intro h
  have := certificate7314
  rw [h.1] at this
  norm_num at this
def C7315 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7315 : C7315.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7315 : ¬ (C7315.det = 0 ∧ ∀ i, C7315.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7315
def C7316 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7316 : C7316.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7316 : ¬ (C7316.det = 0 ∧ ∀ i, C7316.adjugate i i ≠ 0) := by
  intro h
  have := certificate7316
  rw [h.1] at this
  norm_num at this
def C7317 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7317 : C7317.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7317 : ¬ (C7317.det = 0 ∧ ∀ i, C7317.adjugate i i ≠ 0) := by
  intro h
  have := certificate7317
  rw [h.1] at this
  norm_num at this
def C7318 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7318 : C7318.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7318 : ¬ (C7318.det = 0 ∧ ∀ i, C7318.adjugate i i ≠ 0) := by
  intro h
  have := certificate7318
  rw [h.1] at this
  norm_num at this
def C7319 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7319 : C7319.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7319 : ¬ (C7319.det = 0 ∧ ∀ i, C7319.adjugate i i ≠ 0) := by
  intro h
  have := certificate7319
  rw [h.1] at this
  norm_num at this
def C7320 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7320 : C7320.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7320 : ¬ (C7320.det = 0 ∧ ∀ i, C7320.adjugate i i ≠ 0) := by
  intro h
  have := certificate7320
  rw [h.1] at this
  norm_num at this
def C7321 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7321 : C7321.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7321 : ¬ (C7321.det = 0 ∧ ∀ i, C7321.adjugate i i ≠ 0) := by
  intro h
  have := certificate7321
  rw [h.1] at this
  norm_num at this
def C7322 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7322 : C7322.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7322 : ¬ (C7322.det = 0 ∧ ∀ i, C7322.adjugate i i ≠ 0) := by
  intro h
  have := certificate7322
  rw [h.1] at this
  norm_num at this
def C7323 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7323 : C7323.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7323 : ¬ (C7323.det = 0 ∧ ∀ i, C7323.adjugate i i ≠ 0) := by
  intro h
  have := certificate7323
  rw [h.1] at this
  norm_num at this
def C7324 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7324 : C7324.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7324 : ¬ (C7324.det = 0 ∧ ∀ i, C7324.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7324
def C7325 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7325 : C7325.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7325 : ¬ (C7325.det = 0 ∧ ∀ i, C7325.adjugate i i ≠ 0) := by
  intro h
  have := certificate7325
  rw [h.1] at this
  norm_num at this
def C7326 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7326 : C7326.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7326 : ¬ (C7326.det = 0 ∧ ∀ i, C7326.adjugate i i ≠ 0) := by
  intro h
  have := certificate7326
  rw [h.1] at this
  norm_num at this
def C7327 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7327 : C7327.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7327 : ¬ (C7327.det = 0 ∧ ∀ i, C7327.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7327
end Nut8.NewCertificates0228
