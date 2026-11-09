import VerifiedDet
namespace Nut8.NewCertificates0197
def C6304 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6304 : C6304.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6304 : ¬ (C6304.det = 0 ∧ ∀ i, C6304.adjugate i i ≠ 0) := by
  intro h
  have := certificate6304
  rw [h.1] at this
  norm_num at this
def C6305 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6305 : C6305.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6305 : ¬ (C6305.det = 0 ∧ ∀ i, C6305.adjugate i i ≠ 0) := by
  intro h
  have := certificate6305
  rw [h.1] at this
  norm_num at this
def C6306 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6306 : C6306.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6306 : ¬ (C6306.det = 0 ∧ ∀ i, C6306.adjugate i i ≠ 0) := by
  intro h
  have := certificate6306
  rw [h.1] at this
  norm_num at this
def C6307 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6307 : C6307.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6307 : ¬ (C6307.det = 0 ∧ ∀ i, C6307.adjugate i i ≠ 0) := by
  intro h
  have := certificate6307
  rw [h.1] at this
  norm_num at this
def C6308 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6308 : C6308.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6308 : ¬ (C6308.det = 0 ∧ ∀ i, C6308.adjugate i i ≠ 0) := by
  intro h
  have := certificate6308
  rw [h.1] at this
  norm_num at this
def C6309 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6309 : C6309.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6309 : ¬ (C6309.det = 0 ∧ ∀ i, C6309.adjugate i i ≠ 0) := by
  intro h
  have := certificate6309
  rw [h.1] at this
  norm_num at this
def C6310 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6310 : C6310.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6310 : ¬ (C6310.det = 0 ∧ ∀ i, C6310.adjugate i i ≠ 0) := by
  intro h
  have := certificate6310
  rw [h.1] at this
  norm_num at this
def C6311 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6311 : C6311.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6311 : ¬ (C6311.det = 0 ∧ ∀ i, C6311.adjugate i i ≠ 0) := by
  intro h
  have := certificate6311
  rw [h.1] at this
  norm_num at this
def C6312 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6312 : C6312.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6312 : ¬ (C6312.det = 0 ∧ ∀ i, C6312.adjugate i i ≠ 0) := by
  intro h
  have := certificate6312
  rw [h.1] at this
  norm_num at this
def C6313 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate6313 : C6313.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6313 : ¬ (C6313.det = 0 ∧ ∀ i, C6313.adjugate i i ≠ 0) := by
  intro h
  have := certificate6313
  rw [h.1] at this
  norm_num at this
def C6314 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6314 : C6314.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6314 : ¬ (C6314.det = 0 ∧ ∀ i, C6314.adjugate i i ≠ 0) := by
  intro h
  have := certificate6314
  rw [h.1] at this
  norm_num at this
def C6315 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate6315 : C6315.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6315 : ¬ (C6315.det = 0 ∧ ∀ i, C6315.adjugate i i ≠ 0) := by
  intro h
  have := certificate6315
  rw [h.1] at this
  norm_num at this
def C6316 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6316 : C6316.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6316 : ¬ (C6316.det = 0 ∧ ∀ i, C6316.adjugate i i ≠ 0) := by
  intro h
  have := certificate6316
  rw [h.1] at this
  norm_num at this
def C6317 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6317 : C6317.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6317 : ¬ (C6317.det = 0 ∧ ∀ i, C6317.adjugate i i ≠ 0) := by
  intro h
  have := certificate6317
  rw [h.1] at this
  norm_num at this
def C6318 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6318 : C6318.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6318 : ¬ (C6318.det = 0 ∧ ∀ i, C6318.adjugate i i ≠ 0) := by
  intro h
  have := certificate6318
  rw [h.1] at this
  norm_num at this
def C6319 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6319 : C6319.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6319 : ¬ (C6319.det = 0 ∧ ∀ i, C6319.adjugate i i ≠ 0) := by
  intro h
  have := certificate6319
  rw [h.1] at this
  norm_num at this
def C6320 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6320 : C6320.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6320 : ¬ (C6320.det = 0 ∧ ∀ i, C6320.adjugate i i ≠ 0) := by
  intro h
  have := certificate6320
  rw [h.1] at this
  norm_num at this
def C6321 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate6321 : C6321.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6321 : ¬ (C6321.det = 0 ∧ ∀ i, C6321.adjugate i i ≠ 0) := by
  intro h
  have := certificate6321
  rw [h.1] at this
  norm_num at this
def C6322 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6322 : C6322.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6322 : ¬ (C6322.det = 0 ∧ ∀ i, C6322.adjugate i i ≠ 0) := by
  intro h
  have := certificate6322
  rw [h.1] at this
  norm_num at this
def C6323 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate6323 : C6323.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6323 : ¬ (C6323.det = 0 ∧ ∀ i, C6323.adjugate i i ≠ 0) := by
  intro h
  have := certificate6323
  rw [h.1] at this
  norm_num at this
def C6324 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6324 : C6324.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6324 : ¬ (C6324.det = 0 ∧ ∀ i, C6324.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6324
def C6325 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6325 : C6325.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6325 : ¬ (C6325.det = 0 ∧ ∀ i, C6325.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6325
def C6326 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6326 : C6326.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6326 : ¬ (C6326.det = 0 ∧ ∀ i, C6326.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6326
def C6327 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6327 : C6327.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6327 : ¬ (C6327.det = 0 ∧ ∀ i, C6327.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6327
def C6328 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6328 : C6328.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6328 : ¬ (C6328.det = 0 ∧ ∀ i, C6328.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6328
def C6329 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6329 : C6329.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6329 : ¬ (C6329.det = 0 ∧ ∀ i, C6329.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6329
def C6330 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6330 : C6330.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6330 : ¬ (C6330.det = 0 ∧ ∀ i, C6330.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6330
def C6331 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6331 : C6331.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6331 : ¬ (C6331.det = 0 ∧ ∀ i, C6331.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6331
def C6332 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6332 : C6332.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6332 : ¬ (C6332.det = 0 ∧ ∀ i, C6332.adjugate i i ≠ 0) := by
  intro h
  have := certificate6332
  rw [h.1] at this
  norm_num at this
def C6333 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6333 : C6333.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6333 : ¬ (C6333.det = 0 ∧ ∀ i, C6333.adjugate i i ≠ 0) := by
  intro h
  have := certificate6333
  rw [h.1] at this
  norm_num at this
def C6334 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6334 : C6334.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6334 : ¬ (C6334.det = 0 ∧ ∀ i, C6334.adjugate i i ≠ 0) := by
  intro h
  have := certificate6334
  rw [h.1] at this
  norm_num at this
def C6335 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6335 : C6335.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6335 : ¬ (C6335.det = 0 ∧ ∀ i, C6335.adjugate i i ≠ 0) := by
  intro h
  have := certificate6335
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0197
