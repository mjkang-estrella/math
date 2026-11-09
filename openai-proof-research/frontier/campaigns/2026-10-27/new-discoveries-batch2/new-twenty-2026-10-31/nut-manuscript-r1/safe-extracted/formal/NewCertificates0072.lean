import VerifiedDet
namespace Nut8.NewCertificates0072
def C2304 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2304 : C2304.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2304 : ¬ (C2304.det = 0 ∧ ∀ i, C2304.adjugate i i ≠ 0) := by
  intro h
  have := certificate2304
  rw [h.1] at this
  norm_num at this
def C2305 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2305 : C2305.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2305 : ¬ (C2305.det = 0 ∧ ∀ i, C2305.adjugate i i ≠ 0) := by
  intro h
  have := certificate2305
  rw [h.1] at this
  norm_num at this
def C2306 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2306 : C2306.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2306 : ¬ (C2306.det = 0 ∧ ∀ i, C2306.adjugate i i ≠ 0) := by
  intro h
  have := certificate2306
  rw [h.1] at this
  norm_num at this
def C2307 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2307 : C2307.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2307 : ¬ (C2307.det = 0 ∧ ∀ i, C2307.adjugate i i ≠ 0) := by
  intro h
  have := certificate2307
  rw [h.1] at this
  norm_num at this
def C2308 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2308 : C2308.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2308 : ¬ (C2308.det = 0 ∧ ∀ i, C2308.adjugate i i ≠ 0) := by
  intro h
  have := certificate2308
  rw [h.1] at this
  norm_num at this
def C2309 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2309 : C2309.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2309 : ¬ (C2309.det = 0 ∧ ∀ i, C2309.adjugate i i ≠ 0) := by
  intro h
  have := certificate2309
  rw [h.1] at this
  norm_num at this
def C2310 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2310 : C2310.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2310 : ¬ (C2310.det = 0 ∧ ∀ i, C2310.adjugate i i ≠ 0) := by
  intro h
  have := certificate2310
  rw [h.1] at this
  norm_num at this
def C2311 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2311 : C2311.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2311 : ¬ (C2311.det = 0 ∧ ∀ i, C2311.adjugate i i ≠ 0) := by
  intro h
  have := certificate2311
  rw [h.1] at this
  norm_num at this
def C2312 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2312 : C2312.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2312 : ¬ (C2312.det = 0 ∧ ∀ i, C2312.adjugate i i ≠ 0) := by
  intro h
  have := certificate2312
  rw [h.1] at this
  norm_num at this
def C2313 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2313 : C2313.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2313 : ¬ (C2313.det = 0 ∧ ∀ i, C2313.adjugate i i ≠ 0) := by
  intro h
  have := certificate2313
  rw [h.1] at this
  norm_num at this
def C2314 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2314 : C2314.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2314 : ¬ (C2314.det = 0 ∧ ∀ i, C2314.adjugate i i ≠ 0) := by
  intro h
  have := certificate2314
  rw [h.1] at this
  norm_num at this
def C2315 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2315 : C2315.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2315 : ¬ (C2315.det = 0 ∧ ∀ i, C2315.adjugate i i ≠ 0) := by
  intro h
  have := certificate2315
  rw [h.1] at this
  norm_num at this
def C2316 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2316 : C2316.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2316 : ¬ (C2316.det = 0 ∧ ∀ i, C2316.adjugate i i ≠ 0) := by
  intro h
  have := certificate2316
  rw [h.1] at this
  norm_num at this
def C2317 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2317 : C2317.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2317 : ¬ (C2317.det = 0 ∧ ∀ i, C2317.adjugate i i ≠ 0) := by
  intro h
  have := certificate2317
  rw [h.1] at this
  norm_num at this
def C2318 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2318 : C2318.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2318 : ¬ (C2318.det = 0 ∧ ∀ i, C2318.adjugate i i ≠ 0) := by
  intro h
  have := certificate2318
  rw [h.1] at this
  norm_num at this
def C2319 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2319 : C2319.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2319 : ¬ (C2319.det = 0 ∧ ∀ i, C2319.adjugate i i ≠ 0) := by
  intro h
  have := certificate2319
  rw [h.1] at this
  norm_num at this
def C2320 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2320 : C2320.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2320 : ¬ (C2320.det = 0 ∧ ∀ i, C2320.adjugate i i ≠ 0) := by
  intro h
  have := certificate2320
  rw [h.1] at this
  norm_num at this
def C2321 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2321 : C2321.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2321 : ¬ (C2321.det = 0 ∧ ∀ i, C2321.adjugate i i ≠ 0) := by
  intro h
  have := certificate2321
  rw [h.1] at this
  norm_num at this
def C2322 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2322 : C2322.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2322 : ¬ (C2322.det = 0 ∧ ∀ i, C2322.adjugate i i ≠ 0) := by
  intro h
  have := certificate2322
  rw [h.1] at this
  norm_num at this
def C2323 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2323 : C2323.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2323 : ¬ (C2323.det = 0 ∧ ∀ i, C2323.adjugate i i ≠ 0) := by
  intro h
  have := certificate2323
  rw [h.1] at this
  norm_num at this
def C2324 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2324 : C2324.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2324 : ¬ (C2324.det = 0 ∧ ∀ i, C2324.adjugate i i ≠ 0) := by
  intro h
  have := certificate2324
  rw [h.1] at this
  norm_num at this
def C2325 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2325 : C2325.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2325 : ¬ (C2325.det = 0 ∧ ∀ i, C2325.adjugate i i ≠ 0) := by
  intro h
  have := certificate2325
  rw [h.1] at this
  norm_num at this
def C2326 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2326 : C2326.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2326 : ¬ (C2326.det = 0 ∧ ∀ i, C2326.adjugate i i ≠ 0) := by
  intro h
  have := certificate2326
  rw [h.1] at this
  norm_num at this
def C2327 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2327 : C2327.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2327 : ¬ (C2327.det = 0 ∧ ∀ i, C2327.adjugate i i ≠ 0) := by
  intro h
  have := certificate2327
  rw [h.1] at this
  norm_num at this
def C2328 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2328 : C2328.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2328 : ¬ (C2328.det = 0 ∧ ∀ i, C2328.adjugate i i ≠ 0) := by
  intro h
  have := certificate2328
  rw [h.1] at this
  norm_num at this
def C2329 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2329 : C2329.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2329 : ¬ (C2329.det = 0 ∧ ∀ i, C2329.adjugate i i ≠ 0) := by
  intro h
  have := certificate2329
  rw [h.1] at this
  norm_num at this
def C2330 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2330 : C2330.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2330 : ¬ (C2330.det = 0 ∧ ∀ i, C2330.adjugate i i ≠ 0) := by
  intro h
  have := certificate2330
  rw [h.1] at this
  norm_num at this
def C2331 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2331 : C2331.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2331 : ¬ (C2331.det = 0 ∧ ∀ i, C2331.adjugate i i ≠ 0) := by
  intro h
  have := certificate2331
  rw [h.1] at this
  norm_num at this
def C2332 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2332 : C2332.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2332 : ¬ (C2332.det = 0 ∧ ∀ i, C2332.adjugate i i ≠ 0) := by
  intro h
  have := certificate2332
  rw [h.1] at this
  norm_num at this
def C2333 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2333 : C2333.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2333 : ¬ (C2333.det = 0 ∧ ∀ i, C2333.adjugate i i ≠ 0) := by
  intro h
  have := certificate2333
  rw [h.1] at this
  norm_num at this
def C2334 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2334 : C2334.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2334 : ¬ (C2334.det = 0 ∧ ∀ i, C2334.adjugate i i ≠ 0) := by
  intro h
  have := certificate2334
  rw [h.1] at this
  norm_num at this
def C2335 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2335 : C2335.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2335 : ¬ (C2335.det = 0 ∧ ∀ i, C2335.adjugate i i ≠ 0) := by
  intro h
  have := certificate2335
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0072
