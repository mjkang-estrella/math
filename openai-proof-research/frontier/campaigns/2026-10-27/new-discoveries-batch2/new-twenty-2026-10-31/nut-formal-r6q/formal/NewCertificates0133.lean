import VerifiedDet
namespace Nut8.NewCertificates0133
def C4256 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4256 : C4256.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4256 : ¬ (C4256.det = 0 ∧ ∀ i, C4256.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4256
def C4257 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4257 : C4257.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4257 : ¬ (C4257.det = 0 ∧ ∀ i, C4257.adjugate i i ≠ 0) := by
  intro h
  have := certificate4257
  rw [h.1] at this
  norm_num at this
def C4258 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4258 : C4258.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4258 : ¬ (C4258.det = 0 ∧ ∀ i, C4258.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4258
def C4259 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4259 : C4259.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4259 : ¬ (C4259.det = 0 ∧ ∀ i, C4259.adjugate i i ≠ 0) := by
  intro h
  have := certificate4259
  rw [h.1] at this
  norm_num at this
def C4260 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4260 : C4260.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4260 : ¬ (C4260.det = 0 ∧ ∀ i, C4260.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4260
def C4261 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4261 : C4261.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4261 : ¬ (C4261.det = 0 ∧ ∀ i, C4261.adjugate i i ≠ 0) := by
  intro h
  have := certificate4261
  rw [h.1] at this
  norm_num at this
def C4262 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4262 : C4262.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4262 : ¬ (C4262.det = 0 ∧ ∀ i, C4262.adjugate i i ≠ 0) := by
  intro h
  have := certificate4262
  rw [h.1] at this
  norm_num at this
def C4263 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4263 : C4263.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4263 : ¬ (C4263.det = 0 ∧ ∀ i, C4263.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4263
def C4264 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4264 : C4264.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4264 : ¬ (C4264.det = 0 ∧ ∀ i, C4264.adjugate i i ≠ 0) := by
  intro h
  have := certificate4264
  rw [h.1] at this
  norm_num at this
def C4265 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4265 : C4265.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4265 : ¬ (C4265.det = 0 ∧ ∀ i, C4265.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4265
def C4266 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4266 : C4266.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4266 : ¬ (C4266.det = 0 ∧ ∀ i, C4266.adjugate i i ≠ 0) := by
  intro h
  have := certificate4266
  rw [h.1] at this
  norm_num at this
def C4267 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4267 : C4267.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4267 : ¬ (C4267.det = 0 ∧ ∀ i, C4267.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4267
def C4268 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4268 : C4268.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4268 : ¬ (C4268.det = 0 ∧ ∀ i, C4268.adjugate i i ≠ 0) := by
  intro h
  have := certificate4268
  rw [h.1] at this
  norm_num at this
def C4269 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4269 : C4269.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4269 : ¬ (C4269.det = 0 ∧ ∀ i, C4269.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4269
def C4270 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate4270 : C4270.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4270 : ¬ (C4270.det = 0 ∧ ∀ i, C4270.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4270
def C4271 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate4271 : C4271.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4271 : ¬ (C4271.det = 0 ∧ ∀ i, C4271.adjugate i i ≠ 0) := by
  intro h
  have := certificate4271
  rw [h.1] at this
  norm_num at this
def C4272 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate4272 : C4272.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4272 : ¬ (C4272.det = 0 ∧ ∀ i, C4272.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4272
def C4273 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate4273 : C4273.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4273 : ¬ (C4273.det = 0 ∧ ∀ i, C4273.adjugate i i ≠ 0) := by
  intro h
  have := certificate4273
  rw [h.1] at this
  norm_num at this
def C4274 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate4274 : C4274.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4274 : ¬ (C4274.det = 0 ∧ ∀ i, C4274.adjugate i i ≠ 0) := by
  intro h
  have := certificate4274
  rw [h.1] at this
  norm_num at this
def C4275 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate4275 : C4275.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4275 : ¬ (C4275.det = 0 ∧ ∀ i, C4275.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4275
def C4276 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate4276 : C4276.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4276 : ¬ (C4276.det = 0 ∧ ∀ i, C4276.adjugate i i ≠ 0) := by
  intro h
  have := certificate4276
  rw [h.1] at this
  norm_num at this
def C4277 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate4277 : C4277.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4277 : ¬ (C4277.det = 0 ∧ ∀ i, C4277.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4277
def C4278 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate4278 : C4278.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4278 : ¬ (C4278.det = 0 ∧ ∀ i, C4278.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4278
def C4279 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate4279 : C4279.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4279 : ¬ (C4279.det = 0 ∧ ∀ i, C4279.adjugate i i ≠ 0) := by
  intro h
  have := certificate4279
  rw [h.1] at this
  norm_num at this
def C4280 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate4280 : C4280.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4280 : ¬ (C4280.det = 0 ∧ ∀ i, C4280.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4280
def C4281 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate4281 : C4281.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4281 : ¬ (C4281.det = 0 ∧ ∀ i, C4281.adjugate i i ≠ 0) := by
  intro h
  have := certificate4281
  rw [h.1] at this
  norm_num at this
def C4282 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate4282 : C4282.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4282 : ¬ (C4282.det = 0 ∧ ∀ i, C4282.adjugate i i ≠ 0) := by
  intro h
  have := certificate4282
  rw [h.1] at this
  norm_num at this
def C4283 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate4283 : C4283.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4283 : ¬ (C4283.det = 0 ∧ ∀ i, C4283.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4283
def C4284 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate4284 : C4284.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4284 : ¬ (C4284.det = 0 ∧ ∀ i, C4284.adjugate i i ≠ 0) := by
  intro h
  have := certificate4284
  rw [h.1] at this
  norm_num at this
def C4285 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate4285 : C4285.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4285 : ¬ (C4285.det = 0 ∧ ∀ i, C4285.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4285
def C4286 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4286 : C4286.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4286 : ¬ (C4286.det = 0 ∧ ∀ i, C4286.adjugate i i ≠ 0) := by
  intro h
  have := certificate4286
  rw [h.1] at this
  norm_num at this
def C4287 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4287 : C4287.det = (-80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4287 : ¬ (C4287.det = 0 ∧ ∀ i, C4287.adjugate i i ≠ 0) := by
  intro h
  have := certificate4287
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0133
