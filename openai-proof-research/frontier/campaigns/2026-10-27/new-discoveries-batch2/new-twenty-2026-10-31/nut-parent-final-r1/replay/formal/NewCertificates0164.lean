import VerifiedDet
namespace Nut8.NewCertificates0164
def C5248 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5248 : C5248.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5248 : ¬ (C5248.det = 0 ∧ ∀ i, C5248.adjugate i i ≠ 0) := by
  intro h
  have := certificate5248
  rw [h.1] at this
  norm_num at this
def C5249 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5249 : C5249.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5249 : ¬ (C5249.det = 0 ∧ ∀ i, C5249.adjugate i i ≠ 0) := by
  intro h
  have := certificate5249
  rw [h.1] at this
  norm_num at this
def C5250 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5250 : C5250.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5250 : ¬ (C5250.det = 0 ∧ ∀ i, C5250.adjugate i i ≠ 0) := by
  intro h
  have := certificate5250
  rw [h.1] at this
  norm_num at this
def C5251 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5251 : C5251.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5251 : ¬ (C5251.det = 0 ∧ ∀ i, C5251.adjugate i i ≠ 0) := by
  intro h
  have := certificate5251
  rw [h.1] at this
  norm_num at this
def C5252 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5252 : C5252.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5252 : ¬ (C5252.det = 0 ∧ ∀ i, C5252.adjugate i i ≠ 0) := by
  intro h
  have := certificate5252
  rw [h.1] at this
  norm_num at this
def C5253 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5253 : C5253.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5253 : ¬ (C5253.det = 0 ∧ ∀ i, C5253.adjugate i i ≠ 0) := by
  intro h
  have := certificate5253
  rw [h.1] at this
  norm_num at this
def C5254 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5254 : C5254.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5254 : ¬ (C5254.det = 0 ∧ ∀ i, C5254.adjugate i i ≠ 0) := by
  intro h
  have := certificate5254
  rw [h.1] at this
  norm_num at this
def C5255 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5255 : C5255.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5255 : ¬ (C5255.det = 0 ∧ ∀ i, C5255.adjugate i i ≠ 0) := by
  intro h
  have := certificate5255
  rw [h.1] at this
  norm_num at this
def C5256 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5256 : C5256.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5256 : ¬ (C5256.det = 0 ∧ ∀ i, C5256.adjugate i i ≠ 0) := by
  intro h
  have := certificate5256
  rw [h.1] at this
  norm_num at this
def C5257 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5257 : C5257.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5257 : ¬ (C5257.det = 0 ∧ ∀ i, C5257.adjugate i i ≠ 0) := by
  intro h
  have := certificate5257
  rw [h.1] at this
  norm_num at this
def C5258 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5258 : C5258.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5258 : ¬ (C5258.det = 0 ∧ ∀ i, C5258.adjugate i i ≠ 0) := by
  intro h
  have := certificate5258
  rw [h.1] at this
  norm_num at this
def C5259 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5259 : C5259.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5259 : ¬ (C5259.det = 0 ∧ ∀ i, C5259.adjugate i i ≠ 0) := by
  intro h
  have := certificate5259
  rw [h.1] at this
  norm_num at this
def C5260 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5260 : C5260.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5260 : ¬ (C5260.det = 0 ∧ ∀ i, C5260.adjugate i i ≠ 0) := by
  intro h
  have := certificate5260
  rw [h.1] at this
  norm_num at this
def C5261 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5261 : C5261.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5261 : ¬ (C5261.det = 0 ∧ ∀ i, C5261.adjugate i i ≠ 0) := by
  intro h
  have := certificate5261
  rw [h.1] at this
  norm_num at this
def C5262 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5262 : C5262.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5262 : ¬ (C5262.det = 0 ∧ ∀ i, C5262.adjugate i i ≠ 0) := by
  intro h
  have := certificate5262
  rw [h.1] at this
  norm_num at this
def C5263 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5263 : C5263.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5263 : ¬ (C5263.det = 0 ∧ ∀ i, C5263.adjugate i i ≠ 0) := by
  intro h
  have := certificate5263
  rw [h.1] at this
  norm_num at this
def C5264 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5264 : C5264.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5264 : ¬ (C5264.det = 0 ∧ ∀ i, C5264.adjugate i i ≠ 0) := by
  intro h
  have := certificate5264
  rw [h.1] at this
  norm_num at this
def C5265 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5265 : C5265.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5265 : ¬ (C5265.det = 0 ∧ ∀ i, C5265.adjugate i i ≠ 0) := by
  intro h
  have := certificate5265
  rw [h.1] at this
  norm_num at this
def C5266 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5266 : C5266.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5266 : ¬ (C5266.det = 0 ∧ ∀ i, C5266.adjugate i i ≠ 0) := by
  intro h
  have := certificate5266
  rw [h.1] at this
  norm_num at this
def C5267 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5267 : C5267.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5267 : ¬ (C5267.det = 0 ∧ ∀ i, C5267.adjugate i i ≠ 0) := by
  intro h
  have := certificate5267
  rw [h.1] at this
  norm_num at this
def C5268 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5268 : C5268.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5268 : ¬ (C5268.det = 0 ∧ ∀ i, C5268.adjugate i i ≠ 0) := by
  intro h
  have := certificate5268
  rw [h.1] at this
  norm_num at this
def C5269 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5269 : C5269.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5269 : ¬ (C5269.det = 0 ∧ ∀ i, C5269.adjugate i i ≠ 0) := by
  intro h
  have := certificate5269
  rw [h.1] at this
  norm_num at this
def C5270 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5270 : C5270.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5270 : ¬ (C5270.det = 0 ∧ ∀ i, C5270.adjugate i i ≠ 0) := by
  intro h
  have := certificate5270
  rw [h.1] at this
  norm_num at this
def C5271 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5271 : C5271.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5271 : ¬ (C5271.det = 0 ∧ ∀ i, C5271.adjugate i i ≠ 0) := by
  intro h
  have := certificate5271
  rw [h.1] at this
  norm_num at this
def C5272 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5272 : C5272.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5272 : ¬ (C5272.det = 0 ∧ ∀ i, C5272.adjugate i i ≠ 0) := by
  intro h
  have := certificate5272
  rw [h.1] at this
  norm_num at this
def C5273 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5273 : C5273.det = (41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5273 : ¬ (C5273.det = 0 ∧ ∀ i, C5273.adjugate i i ≠ 0) := by
  intro h
  have := certificate5273
  rw [h.1] at this
  norm_num at this
def C5274 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5274 : C5274.det = (41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5274 : ¬ (C5274.det = 0 ∧ ∀ i, C5274.adjugate i i ≠ 0) := by
  intro h
  have := certificate5274
  rw [h.1] at this
  norm_num at this
def C5275 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5275 : C5275.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5275 : ¬ (C5275.det = 0 ∧ ∀ i, C5275.adjugate i i ≠ 0) := by
  intro h
  have := certificate5275
  rw [h.1] at this
  norm_num at this
def C5276 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5276 : C5276.det = (-95 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5276 : ¬ (C5276.det = 0 ∧ ∀ i, C5276.adjugate i i ≠ 0) := by
  intro h
  have := certificate5276
  rw [h.1] at this
  norm_num at this
def C5277 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5277 : C5277.det = (113 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5277 : ¬ (C5277.det = 0 ∧ ∀ i, C5277.adjugate i i ≠ 0) := by
  intro h
  have := certificate5277
  rw [h.1] at this
  norm_num at this
def C5278 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5278 : C5278.det = (113 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5278 : ¬ (C5278.det = 0 ∧ ∀ i, C5278.adjugate i i ≠ 0) := by
  intro h
  have := certificate5278
  rw [h.1] at this
  norm_num at this
def C5279 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5279 : C5279.det = (-95 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5279 : ¬ (C5279.det = 0 ∧ ∀ i, C5279.adjugate i i ≠ 0) := by
  intro h
  have := certificate5279
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0164
