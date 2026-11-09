import VerifiedDet
namespace Nut8.NewCertificates0195
def C6240 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6240 : C6240.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6240 : ¬ (C6240.det = 0 ∧ ∀ i, C6240.adjugate i i ≠ 0) := by
  intro h
  have := certificate6240
  rw [h.1] at this
  norm_num at this
def C6241 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6241 : C6241.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6241 : ¬ (C6241.det = 0 ∧ ∀ i, C6241.adjugate i i ≠ 0) := by
  intro h
  have := certificate6241
  rw [h.1] at this
  norm_num at this
def C6242 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6242 : C6242.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6242 : ¬ (C6242.det = 0 ∧ ∀ i, C6242.adjugate i i ≠ 0) := by
  intro h
  have := certificate6242
  rw [h.1] at this
  norm_num at this
def C6243 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6243 : C6243.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6243 : ¬ (C6243.det = 0 ∧ ∀ i, C6243.adjugate i i ≠ 0) := by
  intro h
  have := certificate6243
  rw [h.1] at this
  norm_num at this
def C6244 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0]
theorem certificate6244 : C6244.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6244 : ¬ (C6244.det = 0 ∧ ∀ i, C6244.adjugate i i ≠ 0) := by
  intro h
  have := certificate6244
  rw [h.1] at this
  norm_num at this
def C6245 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0]
theorem certificate6245 : C6245.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6245 : ¬ (C6245.det = 0 ∧ ∀ i, C6245.adjugate i i ≠ 0) := by
  intro h
  have := certificate6245
  rw [h.1] at this
  norm_num at this
def C6246 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0]
theorem certificate6246 : C6246.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6246 : ¬ (C6246.det = 0 ∧ ∀ i, C6246.adjugate i i ≠ 0) := by
  intro h
  have := certificate6246
  rw [h.1] at this
  norm_num at this
def C6247 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0]
theorem certificate6247 : C6247.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6247 : ¬ (C6247.det = 0 ∧ ∀ i, C6247.adjugate i i ≠ 0) := by
  intro h
  have := certificate6247
  rw [h.1] at this
  norm_num at this
def C6248 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 2, -1, 0, 0, 0]
theorem certificate6248 : C6248.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6248 : ¬ (C6248.det = 0 ∧ ∀ i, C6248.adjugate i i ≠ 0) := by
  intro h
  have := certificate6248
  rw [h.1] at this
  norm_num at this
def C6249 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 2, -1, 0, 0, 0]
theorem certificate6249 : C6249.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6249 : ¬ (C6249.det = 0 ∧ ∀ i, C6249.adjugate i i ≠ 0) := by
  intro h
  have := certificate6249
  rw [h.1] at this
  norm_num at this
def C6250 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 2, -1, 0, 0, 0]
theorem certificate6250 : C6250.det = (-38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6250 : ¬ (C6250.det = 0 ∧ ∀ i, C6250.adjugate i i ≠ 0) := by
  intro h
  have := certificate6250
  rw [h.1] at this
  norm_num at this
def C6251 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 2, -1, 0, 0, 0]
theorem certificate6251 : C6251.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6251 : ¬ (C6251.det = 0 ∧ ∀ i, C6251.adjugate i i ≠ 0) := by
  intro h
  have := certificate6251
  rw [h.1] at this
  norm_num at this
def C6252 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0]
theorem certificate6252 : C6252.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6252 : ¬ (C6252.det = 0 ∧ ∀ i, C6252.adjugate i i ≠ 0) := by
  intro h
  have := certificate6252
  rw [h.1] at this
  norm_num at this
def C6253 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0]
theorem certificate6253 : C6253.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6253 : ¬ (C6253.det = 0 ∧ ∀ i, C6253.adjugate i i ≠ 0) := by
  intro h
  have := certificate6253
  rw [h.1] at this
  norm_num at this
def C6254 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0]
theorem certificate6254 : C6254.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6254 : ¬ (C6254.det = 0 ∧ ∀ i, C6254.adjugate i i ≠ 0) := by
  intro h
  have := certificate6254
  rw [h.1] at this
  norm_num at this
def C6255 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0]
theorem certificate6255 : C6255.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6255 : ¬ (C6255.det = 0 ∧ ∀ i, C6255.adjugate i i ≠ 0) := by
  intro h
  have := certificate6255
  rw [h.1] at this
  norm_num at this
def C6256 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 2, -1, 0, 0, 0]
theorem certificate6256 : C6256.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6256 : ¬ (C6256.det = 0 ∧ ∀ i, C6256.adjugate i i ≠ 0) := by
  intro h
  have := certificate6256
  rw [h.1] at this
  norm_num at this
def C6257 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 2, -1, 0, 0, 0]
theorem certificate6257 : C6257.det = (-38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6257 : ¬ (C6257.det = 0 ∧ ∀ i, C6257.adjugate i i ≠ 0) := by
  intro h
  have := certificate6257
  rw [h.1] at this
  norm_num at this
def C6258 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 2, -1, 0, 0, 0]
theorem certificate6258 : C6258.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6258 : ¬ (C6258.det = 0 ∧ ∀ i, C6258.adjugate i i ≠ 0) := by
  intro h
  have := certificate6258
  rw [h.1] at this
  norm_num at this
def C6259 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 2, -1, 0, 0, 0]
theorem certificate6259 : C6259.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6259 : ¬ (C6259.det = 0 ∧ ∀ i, C6259.adjugate i i ≠ 0) := by
  intro h
  have := certificate6259
  rw [h.1] at this
  norm_num at this
def C6260 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6260 : C6260.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6260 : ¬ (C6260.det = 0 ∧ ∀ i, C6260.adjugate i i ≠ 0) := by
  intro h
  have := certificate6260
  rw [h.1] at this
  norm_num at this
def C6261 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6261 : C6261.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6261 : ¬ (C6261.det = 0 ∧ ∀ i, C6261.adjugate i i ≠ 0) := by
  intro h
  have := certificate6261
  rw [h.1] at this
  norm_num at this
def C6262 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6262 : C6262.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6262 : ¬ (C6262.det = 0 ∧ ∀ i, C6262.adjugate i i ≠ 0) := by
  intro h
  have := certificate6262
  rw [h.1] at this
  norm_num at this
def C6263 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6263 : C6263.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6263 : ¬ (C6263.det = 0 ∧ ∀ i, C6263.adjugate i i ≠ 0) := by
  intro h
  have := certificate6263
  rw [h.1] at this
  norm_num at this
def C6264 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6264 : C6264.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6264 : ¬ (C6264.det = 0 ∧ ∀ i, C6264.adjugate i i ≠ 0) := by
  intro h
  have := certificate6264
  rw [h.1] at this
  norm_num at this
def C6265 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6265 : C6265.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6265 : ¬ (C6265.det = 0 ∧ ∀ i, C6265.adjugate i i ≠ 0) := by
  intro h
  have := certificate6265
  rw [h.1] at this
  norm_num at this
def C6266 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6266 : C6266.det = (-27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6266 : ¬ (C6266.det = 0 ∧ ∀ i, C6266.adjugate i i ≠ 0) := by
  intro h
  have := certificate6266
  rw [h.1] at this
  norm_num at this
def C6267 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6267 : C6267.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6267 : ¬ (C6267.det = 0 ∧ ∀ i, C6267.adjugate i i ≠ 0) := by
  intro h
  have := certificate6267
  rw [h.1] at this
  norm_num at this
def C6268 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6268 : C6268.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6268 : ¬ (C6268.det = 0 ∧ ∀ i, C6268.adjugate i i ≠ 0) := by
  intro h
  have := certificate6268
  rw [h.1] at this
  norm_num at this
def C6269 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6269 : C6269.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6269 : ¬ (C6269.det = 0 ∧ ∀ i, C6269.adjugate i i ≠ 0) := by
  intro h
  have := certificate6269
  rw [h.1] at this
  norm_num at this
def C6270 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6270 : C6270.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6270 : ¬ (C6270.det = 0 ∧ ∀ i, C6270.adjugate i i ≠ 0) := by
  intro h
  have := certificate6270
  rw [h.1] at this
  norm_num at this
def C6271 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6271 : C6271.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6271 : ¬ (C6271.det = 0 ∧ ∀ i, C6271.adjugate i i ≠ 0) := by
  intro h
  have := certificate6271
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0195
