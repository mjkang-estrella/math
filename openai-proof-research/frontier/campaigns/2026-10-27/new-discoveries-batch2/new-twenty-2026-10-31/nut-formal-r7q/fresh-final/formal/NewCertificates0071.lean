import VerifiedDet
namespace Nut8.NewCertificates0071
def C2272 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2272 : C2272.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2272 : ¬ (C2272.det = 0 ∧ ∀ i, C2272.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2272
def C2273 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2273 : C2273.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2273 : ¬ (C2273.det = 0 ∧ ∀ i, C2273.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2273
def C2274 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2274 : C2274.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2274 : ¬ (C2274.det = 0 ∧ ∀ i, C2274.adjugate i i ≠ 0) := by
  intro h
  have := certificate2274
  rw [h.1] at this
  norm_num at this
def C2275 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2275 : C2275.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2275 : ¬ (C2275.det = 0 ∧ ∀ i, C2275.adjugate i i ≠ 0) := by
  intro h
  have := certificate2275
  rw [h.1] at this
  norm_num at this
def C2276 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2276 : C2276.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2276 : ¬ (C2276.det = 0 ∧ ∀ i, C2276.adjugate i i ≠ 0) := by
  intro h
  have := certificate2276
  rw [h.1] at this
  norm_num at this
def C2277 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2277 : C2277.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2277 : ¬ (C2277.det = 0 ∧ ∀ i, C2277.adjugate i i ≠ 0) := by
  intro h
  have := certificate2277
  rw [h.1] at this
  norm_num at this
def C2278 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2278 : C2278.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2278 : ¬ (C2278.det = 0 ∧ ∀ i, C2278.adjugate i i ≠ 0) := by
  intro h
  have := certificate2278
  rw [h.1] at this
  norm_num at this
def C2279 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2279 : C2279.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2279 : ¬ (C2279.det = 0 ∧ ∀ i, C2279.adjugate i i ≠ 0) := by
  intro h
  have := certificate2279
  rw [h.1] at this
  norm_num at this
def C2280 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2280 : C2280.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2280 : ¬ (C2280.det = 0 ∧ ∀ i, C2280.adjugate i i ≠ 0) := by
  intro h
  have := certificate2280
  rw [h.1] at this
  norm_num at this
def C2281 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2281 : C2281.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2281 : ¬ (C2281.det = 0 ∧ ∀ i, C2281.adjugate i i ≠ 0) := by
  intro h
  have := certificate2281
  rw [h.1] at this
  norm_num at this
def C2282 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2282 : C2282.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2282 : ¬ (C2282.det = 0 ∧ ∀ i, C2282.adjugate i i ≠ 0) := by
  intro h
  have := certificate2282
  rw [h.1] at this
  norm_num at this
def C2283 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2283 : C2283.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2283 : ¬ (C2283.det = 0 ∧ ∀ i, C2283.adjugate i i ≠ 0) := by
  intro h
  have := certificate2283
  rw [h.1] at this
  norm_num at this
def C2284 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2284 : C2284.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2284 : ¬ (C2284.det = 0 ∧ ∀ i, C2284.adjugate i i ≠ 0) := by
  intro h
  have := certificate2284
  rw [h.1] at this
  norm_num at this
def C2285 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2285 : C2285.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2285 : ¬ (C2285.det = 0 ∧ ∀ i, C2285.adjugate i i ≠ 0) := by
  intro h
  have := certificate2285
  rw [h.1] at this
  norm_num at this
def C2286 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2286 : C2286.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2286 : ¬ (C2286.det = 0 ∧ ∀ i, C2286.adjugate i i ≠ 0) := by
  intro h
  have := certificate2286
  rw [h.1] at this
  norm_num at this
def C2287 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2287 : C2287.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2287 : ¬ (C2287.det = 0 ∧ ∀ i, C2287.adjugate i i ≠ 0) := by
  intro h
  have := certificate2287
  rw [h.1] at this
  norm_num at this
def C2288 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2288 : C2288.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2288 : ¬ (C2288.det = 0 ∧ ∀ i, C2288.adjugate i i ≠ 0) := by
  intro h
  have := certificate2288
  rw [h.1] at this
  norm_num at this
def C2289 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2289 : C2289.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2289 : ¬ (C2289.det = 0 ∧ ∀ i, C2289.adjugate i i ≠ 0) := by
  intro h
  have := certificate2289
  rw [h.1] at this
  norm_num at this
def C2290 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2290 : C2290.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2290 : ¬ (C2290.det = 0 ∧ ∀ i, C2290.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2290
def C2291 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2291 : C2291.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2291 : ¬ (C2291.det = 0 ∧ ∀ i, C2291.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2291
def C2292 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2292 : C2292.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2292 : ¬ (C2292.det = 0 ∧ ∀ i, C2292.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2292
def C2293 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2293 : C2293.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2293 : ¬ (C2293.det = 0 ∧ ∀ i, C2293.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2293
def C2294 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2294 : C2294.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2294 : ¬ (C2294.det = 0 ∧ ∀ i, C2294.adjugate i i ≠ 0) := by
  intro h
  have := certificate2294
  rw [h.1] at this
  norm_num at this
def C2295 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2295 : C2295.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2295 : ¬ (C2295.det = 0 ∧ ∀ i, C2295.adjugate i i ≠ 0) := by
  intro h
  have := certificate2295
  rw [h.1] at this
  norm_num at this
def C2296 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2296 : C2296.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2296 : ¬ (C2296.det = 0 ∧ ∀ i, C2296.adjugate i i ≠ 0) := by
  intro h
  have := certificate2296
  rw [h.1] at this
  norm_num at this
def C2297 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2297 : C2297.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2297 : ¬ (C2297.det = 0 ∧ ∀ i, C2297.adjugate i i ≠ 0) := by
  intro h
  have := certificate2297
  rw [h.1] at this
  norm_num at this
def C2298 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2298 : C2298.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2298 : ¬ (C2298.det = 0 ∧ ∀ i, C2298.adjugate i i ≠ 0) := by
  intro h
  have := certificate2298
  rw [h.1] at this
  norm_num at this
def C2299 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2299 : C2299.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2299 : ¬ (C2299.det = 0 ∧ ∀ i, C2299.adjugate i i ≠ 0) := by
  intro h
  have := certificate2299
  rw [h.1] at this
  norm_num at this
def C2300 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2300 : C2300.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2300 : ¬ (C2300.det = 0 ∧ ∀ i, C2300.adjugate i i ≠ 0) := by
  intro h
  have := certificate2300
  rw [h.1] at this
  norm_num at this
def C2301 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2301 : C2301.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2301 : ¬ (C2301.det = 0 ∧ ∀ i, C2301.adjugate i i ≠ 0) := by
  intro h
  have := certificate2301
  rw [h.1] at this
  norm_num at this
def C2302 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2302 : C2302.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2302 : ¬ (C2302.det = 0 ∧ ∀ i, C2302.adjugate i i ≠ 0) := by
  intro h
  have := certificate2302
  rw [h.1] at this
  norm_num at this
def C2303 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2303 : C2303.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2303 : ¬ (C2303.det = 0 ∧ ∀ i, C2303.adjugate i i ≠ 0) := by
  intro h
  have := certificate2303
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0071
