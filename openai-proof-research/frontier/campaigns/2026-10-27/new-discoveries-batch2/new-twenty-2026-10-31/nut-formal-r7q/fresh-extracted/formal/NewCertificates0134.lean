import VerifiedDet
namespace Nut8.NewCertificates0134
def C4288 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4288 : C4288.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4288 : ¬ (C4288.det = 0 ∧ ∀ i, C4288.adjugate i i ≠ 0) := by
  intro h
  have := certificate4288
  rw [h.1] at this
  norm_num at this
def C4289 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4289 : C4289.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4289 : ¬ (C4289.det = 0 ∧ ∀ i, C4289.adjugate i i ≠ 0) := by
  intro h
  have := certificate4289
  rw [h.1] at this
  norm_num at this
def C4290 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4290 : C4290.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4290 : ¬ (C4290.det = 0 ∧ ∀ i, C4290.adjugate i i ≠ 0) := by
  intro h
  have := certificate4290
  rw [h.1] at this
  norm_num at this
def C4291 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4291 : C4291.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4291 : ¬ (C4291.det = 0 ∧ ∀ i, C4291.adjugate i i ≠ 0) := by
  intro h
  have := certificate4291
  rw [h.1] at this
  norm_num at this
def C4292 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4292 : C4292.det = (-80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4292 : ¬ (C4292.det = 0 ∧ ∀ i, C4292.adjugate i i ≠ 0) := by
  intro h
  have := certificate4292
  rw [h.1] at this
  norm_num at this
def C4293 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -2, 0, 0; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate4293 : C4293.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4293 : ¬ (C4293.det = 0 ∧ ∀ i, C4293.adjugate i i ≠ 0) := by
  intro h
  have := certificate4293
  rw [h.1] at this
  norm_num at this
def C4294 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate4294 : C4294.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4294 : ¬ (C4294.det = 0 ∧ ∀ i, C4294.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4294
def C4295 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate4295 : C4295.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4295 : ¬ (C4295.det = 0 ∧ ∀ i, C4295.adjugate i i ≠ 0) := by
  intro h
  have := certificate4295
  rw [h.1] at this
  norm_num at this
def C4296 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate4296 : C4296.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4296 : ¬ (C4296.det = 0 ∧ ∀ i, C4296.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4296
def C4297 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate4297 : C4297.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4297 : ¬ (C4297.det = 0 ∧ ∀ i, C4297.adjugate i i ≠ 0) := by
  intro h
  have := certificate4297
  rw [h.1] at this
  norm_num at this
def C4298 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate4298 : C4298.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4298 : ¬ (C4298.det = 0 ∧ ∀ i, C4298.adjugate i i ≠ 0) := by
  intro h
  have := certificate4298
  rw [h.1] at this
  norm_num at this
def C4299 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate4299 : C4299.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4299 : ¬ (C4299.det = 0 ∧ ∀ i, C4299.adjugate i i ≠ 0) := by
  intro h
  have := certificate4299
  rw [h.1] at this
  norm_num at this
def C4300 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate4300 : C4300.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4300 : ¬ (C4300.det = 0 ∧ ∀ i, C4300.adjugate i i ≠ 0) := by
  intro h
  have := certificate4300
  rw [h.1] at this
  norm_num at this
def C4301 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate4301 : C4301.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4301 : ¬ (C4301.det = 0 ∧ ∀ i, C4301.adjugate i i ≠ 0) := by
  intro h
  have := certificate4301
  rw [h.1] at this
  norm_num at this
def C4302 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate4302 : C4302.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4302 : ¬ (C4302.det = 0 ∧ ∀ i, C4302.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4302
def C4303 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate4303 : C4303.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4303 : ¬ (C4303.det = 0 ∧ ∀ i, C4303.adjugate i i ≠ 0) := by
  intro h
  have := certificate4303
  rw [h.1] at this
  norm_num at this
def C4304 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate4304 : C4304.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4304 : ¬ (C4304.det = 0 ∧ ∀ i, C4304.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4304
def C4305 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate4305 : C4305.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4305 : ¬ (C4305.det = 0 ∧ ∀ i, C4305.adjugate i i ≠ 0) := by
  intro h
  have := certificate4305
  rw [h.1] at this
  norm_num at this
def C4306 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate4306 : C4306.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4306 : ¬ (C4306.det = 0 ∧ ∀ i, C4306.adjugate i i ≠ 0) := by
  intro h
  have := certificate4306
  rw [h.1] at this
  norm_num at this
def C4307 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate4307 : C4307.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4307 : ¬ (C4307.det = 0 ∧ ∀ i, C4307.adjugate i i ≠ 0) := by
  intro h
  have := certificate4307
  rw [h.1] at this
  norm_num at this
def C4308 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate4308 : C4308.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4308 : ¬ (C4308.det = 0 ∧ ∀ i, C4308.adjugate i i ≠ 0) := by
  intro h
  have := certificate4308
  rw [h.1] at this
  norm_num at this
def C4309 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate4309 : C4309.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4309 : ¬ (C4309.det = 0 ∧ ∀ i, C4309.adjugate i i ≠ 0) := by
  intro h
  have := certificate4309
  rw [h.1] at this
  norm_num at this
def C4310 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate4310 : C4310.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4310 : ¬ (C4310.det = 0 ∧ ∀ i, C4310.adjugate i i ≠ 0) := by
  intro h
  have := certificate4310
  rw [h.1] at this
  norm_num at this
def C4311 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate4311 : C4311.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4311 : ¬ (C4311.det = 0 ∧ ∀ i, C4311.adjugate i i ≠ 0) := by
  intro h
  have := certificate4311
  rw [h.1] at this
  norm_num at this
def C4312 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate4312 : C4312.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4312 : ¬ (C4312.det = 0 ∧ ∀ i, C4312.adjugate i i ≠ 0) := by
  intro h
  have := certificate4312
  rw [h.1] at this
  norm_num at this
def C4313 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate4313 : C4313.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4313 : ¬ (C4313.det = 0 ∧ ∀ i, C4313.adjugate i i ≠ 0) := by
  intro h
  have := certificate4313
  rw [h.1] at this
  norm_num at this
def C4314 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate4314 : C4314.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4314 : ¬ (C4314.det = 0 ∧ ∀ i, C4314.adjugate i i ≠ 0) := by
  intro h
  have := certificate4314
  rw [h.1] at this
  norm_num at this
def C4315 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate4315 : C4315.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4315 : ¬ (C4315.det = 0 ∧ ∀ i, C4315.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4315
def C4316 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate4316 : C4316.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4316 : ¬ (C4316.det = 0 ∧ ∀ i, C4316.adjugate i i ≠ 0) := by
  intro h
  have := certificate4316
  rw [h.1] at this
  norm_num at this
def C4317 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate4317 : C4317.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4317 : ¬ (C4317.det = 0 ∧ ∀ i, C4317.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4317
def C4318 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate4318 : C4318.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4318 : ¬ (C4318.det = 0 ∧ ∀ i, C4318.adjugate i i ≠ 0) := by
  intro h
  have := certificate4318
  rw [h.1] at this
  norm_num at this
def C4319 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate4319 : C4319.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4319 : ¬ (C4319.det = 0 ∧ ∀ i, C4319.adjugate i i ≠ 0) := by
  intro h
  have := certificate4319
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0134
