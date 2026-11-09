import VerifiedDet
namespace Nut8.NewCertificates0070
def C2240 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2240 : C2240.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2240 : ¬ (C2240.det = 0 ∧ ∀ i, C2240.adjugate i i ≠ 0) := by
  intro h
  have := certificate2240
  rw [h.1] at this
  norm_num at this
def C2241 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2241 : C2241.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2241 : ¬ (C2241.det = 0 ∧ ∀ i, C2241.adjugate i i ≠ 0) := by
  intro h
  have := certificate2241
  rw [h.1] at this
  norm_num at this
def C2242 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2242 : C2242.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2242 : ¬ (C2242.det = 0 ∧ ∀ i, C2242.adjugate i i ≠ 0) := by
  intro h
  have := certificate2242
  rw [h.1] at this
  norm_num at this
def C2243 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2243 : C2243.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2243 : ¬ (C2243.det = 0 ∧ ∀ i, C2243.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate2243
def C2244 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2244 : C2244.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2244 : ¬ (C2244.det = 0 ∧ ∀ i, C2244.adjugate i i ≠ 0) := by
  intro h
  have := certificate2244
  rw [h.1] at this
  norm_num at this
def C2245 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2245 : C2245.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2245 : ¬ (C2245.det = 0 ∧ ∀ i, C2245.adjugate i i ≠ 0) := by
  intro h
  have := certificate2245
  rw [h.1] at this
  norm_num at this
def C2246 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2246 : C2246.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2246 : ¬ (C2246.det = 0 ∧ ∀ i, C2246.adjugate i i ≠ 0) := by
  intro h
  have := certificate2246
  rw [h.1] at this
  norm_num at this
def C2247 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2247 : C2247.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2247 : ¬ (C2247.det = 0 ∧ ∀ i, C2247.adjugate i i ≠ 0) := by
  intro h
  have := certificate2247
  rw [h.1] at this
  norm_num at this
def C2248 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2248 : C2248.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2248 : ¬ (C2248.det = 0 ∧ ∀ i, C2248.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate2248
def C2249 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate2249 : C2249.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2249 : ¬ (C2249.det = 0 ∧ ∀ i, C2249.adjugate i i ≠ 0) := by
  intro h
  have := certificate2249
  rw [h.1] at this
  norm_num at this
def C2250 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2250 : C2250.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2250 : ¬ (C2250.det = 0 ∧ ∀ i, C2250.adjugate i i ≠ 0) := by
  intro h
  have := certificate2250
  rw [h.1] at this
  norm_num at this
def C2251 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2251 : C2251.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2251 : ¬ (C2251.det = 0 ∧ ∀ i, C2251.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate2251
def C2252 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2252 : C2252.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2252 : ¬ (C2252.det = 0 ∧ ∀ i, C2252.adjugate i i ≠ 0) := by
  intro h
  have := certificate2252
  rw [h.1] at this
  norm_num at this
def C2253 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2253 : C2253.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2253 : ¬ (C2253.det = 0 ∧ ∀ i, C2253.adjugate i i ≠ 0) := by
  intro h
  have := certificate2253
  rw [h.1] at this
  norm_num at this
def C2254 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2254 : C2254.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2254 : ¬ (C2254.det = 0 ∧ ∀ i, C2254.adjugate i i ≠ 0) := by
  intro h
  have := certificate2254
  rw [h.1] at this
  norm_num at this
def C2255 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2255 : C2255.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2255 : ¬ (C2255.det = 0 ∧ ∀ i, C2255.adjugate i i ≠ 0) := by
  intro h
  have := certificate2255
  rw [h.1] at this
  norm_num at this
def C2256 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2256 : C2256.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2256 : ¬ (C2256.det = 0 ∧ ∀ i, C2256.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate2256
def C2257 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate2257 : C2257.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2257 : ¬ (C2257.det = 0 ∧ ∀ i, C2257.adjugate i i ≠ 0) := by
  intro h
  have := certificate2257
  rw [h.1] at this
  norm_num at this
def C2258 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2258 : C2258.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2258 : ¬ (C2258.det = 0 ∧ ∀ i, C2258.adjugate i i ≠ 0) := by
  intro h
  have := certificate2258
  rw [h.1] at this
  norm_num at this
def C2259 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2259 : C2259.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2259 : ¬ (C2259.det = 0 ∧ ∀ i, C2259.adjugate i i ≠ 0) := by
  intro h
  have := certificate2259
  rw [h.1] at this
  norm_num at this
def C2260 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2260 : C2260.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2260 : ¬ (C2260.det = 0 ∧ ∀ i, C2260.adjugate i i ≠ 0) := by
  intro h
  have := certificate2260
  rw [h.1] at this
  norm_num at this
def C2261 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2261 : C2261.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2261 : ¬ (C2261.det = 0 ∧ ∀ i, C2261.adjugate i i ≠ 0) := by
  intro h
  have := certificate2261
  rw [h.1] at this
  norm_num at this
def C2262 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2262 : C2262.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2262 : ¬ (C2262.det = 0 ∧ ∀ i, C2262.adjugate i i ≠ 0) := by
  intro h
  have := certificate2262
  rw [h.1] at this
  norm_num at this
def C2263 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2263 : C2263.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2263 : ¬ (C2263.det = 0 ∧ ∀ i, C2263.adjugate i i ≠ 0) := by
  intro h
  have := certificate2263
  rw [h.1] at this
  norm_num at this
def C2264 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2264 : C2264.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2264 : ¬ (C2264.det = 0 ∧ ∀ i, C2264.adjugate i i ≠ 0) := by
  intro h
  have := certificate2264
  rw [h.1] at this
  norm_num at this
def C2265 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate2265 : C2265.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2265 : ¬ (C2265.det = 0 ∧ ∀ i, C2265.adjugate i i ≠ 0) := by
  intro h
  have := certificate2265
  rw [h.1] at this
  norm_num at this
def C2266 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2266 : C2266.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2266 : ¬ (C2266.det = 0 ∧ ∀ i, C2266.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2266
def C2267 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2267 : C2267.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2267 : ¬ (C2267.det = 0 ∧ ∀ i, C2267.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2267
def C2268 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2268 : C2268.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2268 : ¬ (C2268.det = 0 ∧ ∀ i, C2268.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2268
def C2269 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2269 : C2269.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2269 : ¬ (C2269.det = 0 ∧ ∀ i, C2269.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2269
def C2270 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2270 : C2270.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2270 : ¬ (C2270.det = 0 ∧ ∀ i, C2270.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2270
def C2271 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2271 : C2271.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2271 : ¬ (C2271.det = 0 ∧ ∀ i, C2271.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2271
end Nut8.NewCertificates0070
