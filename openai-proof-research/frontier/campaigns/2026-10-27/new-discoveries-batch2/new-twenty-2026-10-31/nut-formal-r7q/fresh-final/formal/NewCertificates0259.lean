import VerifiedDet
namespace Nut8.NewCertificates0259
def C8288 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8288 : C8288.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8288 : ¬ (C8288.det = 0 ∧ ∀ i, C8288.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8288
def C8289 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8289 : C8289.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8289 : ¬ (C8289.det = 0 ∧ ∀ i, C8289.adjugate i i ≠ 0) := by
  intro h
  have := certificate8289
  rw [h.1] at this
  norm_num at this
def C8290 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8290 : C8290.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8290 : ¬ (C8290.det = 0 ∧ ∀ i, C8290.adjugate i i ≠ 0) := by
  intro h
  have := certificate8290
  rw [h.1] at this
  norm_num at this
def C8291 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8291 : C8291.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8291 : ¬ (C8291.det = 0 ∧ ∀ i, C8291.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8291
def C8292 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8292 : C8292.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8292 : ¬ (C8292.det = 0 ∧ ∀ i, C8292.adjugate i i ≠ 0) := by
  intro h
  have := certificate8292
  rw [h.1] at this
  norm_num at this
def C8293 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8293 : C8293.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8293 : ¬ (C8293.det = 0 ∧ ∀ i, C8293.adjugate i i ≠ 0) := by
  intro h
  have := certificate8293
  rw [h.1] at this
  norm_num at this
def C8294 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8294 : C8294.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8294 : ¬ (C8294.det = 0 ∧ ∀ i, C8294.adjugate i i ≠ 0) := by
  intro h
  have := certificate8294
  rw [h.1] at this
  norm_num at this
def C8295 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8295 : C8295.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8295 : ¬ (C8295.det = 0 ∧ ∀ i, C8295.adjugate i i ≠ 0) := by
  intro h
  have := certificate8295
  rw [h.1] at this
  norm_num at this
def C8296 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8296 : C8296.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8296 : ¬ (C8296.det = 0 ∧ ∀ i, C8296.adjugate i i ≠ 0) := by
  intro h
  have := certificate8296
  rw [h.1] at this
  norm_num at this
def C8297 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8297 : C8297.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8297 : ¬ (C8297.det = 0 ∧ ∀ i, C8297.adjugate i i ≠ 0) := by
  intro h
  have := certificate8297
  rw [h.1] at this
  norm_num at this
def C8298 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8298 : C8298.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8298 : ¬ (C8298.det = 0 ∧ ∀ i, C8298.adjugate i i ≠ 0) := by
  intro h
  have := certificate8298
  rw [h.1] at this
  norm_num at this
def C8299 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8299 : C8299.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8299 : ¬ (C8299.det = 0 ∧ ∀ i, C8299.adjugate i i ≠ 0) := by
  intro h
  have := certificate8299
  rw [h.1] at this
  norm_num at this
def C8300 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate8300 : C8300.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8300 : ¬ (C8300.det = 0 ∧ ∀ i, C8300.adjugate i i ≠ 0) := by
  intro h
  have := certificate8300
  rw [h.1] at this
  norm_num at this
def C8301 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate8301 : C8301.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8301 : ¬ (C8301.det = 0 ∧ ∀ i, C8301.adjugate i i ≠ 0) := by
  intro h
  have := certificate8301
  rw [h.1] at this
  norm_num at this
def C8302 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate8302 : C8302.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8302 : ¬ (C8302.det = 0 ∧ ∀ i, C8302.adjugate i i ≠ 0) := by
  intro h
  have := certificate8302
  rw [h.1] at this
  norm_num at this
def C8303 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate8303 : C8303.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8303 : ¬ (C8303.det = 0 ∧ ∀ i, C8303.adjugate i i ≠ 0) := by
  intro h
  have := certificate8303
  rw [h.1] at this
  norm_num at this
def C8304 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate8304 : C8304.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8304 : ¬ (C8304.det = 0 ∧ ∀ i, C8304.adjugate i i ≠ 0) := by
  intro h
  have := certificate8304
  rw [h.1] at this
  norm_num at this
def C8305 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate8305 : C8305.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8305 : ¬ (C8305.det = 0 ∧ ∀ i, C8305.adjugate i i ≠ 0) := by
  intro h
  have := certificate8305
  rw [h.1] at this
  norm_num at this
def C8306 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate8306 : C8306.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8306 : ¬ (C8306.det = 0 ∧ ∀ i, C8306.adjugate i i ≠ 0) := by
  intro h
  have := certificate8306
  rw [h.1] at this
  norm_num at this
def C8307 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate8307 : C8307.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8307 : ¬ (C8307.det = 0 ∧ ∀ i, C8307.adjugate i i ≠ 0) := by
  intro h
  have := certificate8307
  rw [h.1] at this
  norm_num at this
def C8308 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8308 : C8308.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8308 : ¬ (C8308.det = 0 ∧ ∀ i, C8308.adjugate i i ≠ 0) := by
  intro h
  have := certificate8308
  rw [h.1] at this
  norm_num at this
def C8309 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8309 : C8309.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8309 : ¬ (C8309.det = 0 ∧ ∀ i, C8309.adjugate i i ≠ 0) := by
  intro h
  have := certificate8309
  rw [h.1] at this
  norm_num at this
def C8310 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8310 : C8310.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8310 : ¬ (C8310.det = 0 ∧ ∀ i, C8310.adjugate i i ≠ 0) := by
  intro h
  have := certificate8310
  rw [h.1] at this
  norm_num at this
def C8311 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8311 : C8311.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8311 : ¬ (C8311.det = 0 ∧ ∀ i, C8311.adjugate i i ≠ 0) := by
  intro h
  have := certificate8311
  rw [h.1] at this
  norm_num at this
def C8312 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8312 : C8312.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8312 : ¬ (C8312.det = 0 ∧ ∀ i, C8312.adjugate i i ≠ 0) := by
  intro h
  have := certificate8312
  rw [h.1] at this
  norm_num at this
def C8313 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8313 : C8313.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8313 : ¬ (C8313.det = 0 ∧ ∀ i, C8313.adjugate i i ≠ 0) := by
  intro h
  have := certificate8313
  rw [h.1] at this
  norm_num at this
def C8314 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8314 : C8314.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8314 : ¬ (C8314.det = 0 ∧ ∀ i, C8314.adjugate i i ≠ 0) := by
  intro h
  have := certificate8314
  rw [h.1] at this
  norm_num at this
def C8315 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8315 : C8315.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8315 : ¬ (C8315.det = 0 ∧ ∀ i, C8315.adjugate i i ≠ 0) := by
  intro h
  have := certificate8315
  rw [h.1] at this
  norm_num at this
def C8316 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8316 : C8316.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8316 : ¬ (C8316.det = 0 ∧ ∀ i, C8316.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8316
def C8317 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate8317 : C8317.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8317 : ¬ (C8317.det = 0 ∧ ∀ i, C8317.adjugate i i ≠ 0) := by
  intro h
  have := certificate8317
  rw [h.1] at this
  norm_num at this
def C8318 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8318 : C8318.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8318 : ¬ (C8318.det = 0 ∧ ∀ i, C8318.adjugate i i ≠ 0) := by
  intro h
  have := certificate8318
  rw [h.1] at this
  norm_num at this
def C8319 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate8319 : C8319.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8319 : ¬ (C8319.det = 0 ∧ ∀ i, C8319.adjugate i i ≠ 0) := by
  intro h
  have := certificate8319
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0259
