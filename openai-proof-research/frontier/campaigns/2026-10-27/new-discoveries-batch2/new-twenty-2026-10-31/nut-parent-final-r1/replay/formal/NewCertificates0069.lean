import VerifiedDet
namespace Nut8.NewCertificates0069
def C2208 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2208 : C2208.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2208 : ¬ (C2208.det = 0 ∧ ∀ i, C2208.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2208
def C2209 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2209 : C2209.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2209 : ¬ (C2209.det = 0 ∧ ∀ i, C2209.adjugate i i ≠ 0) := by
  intro h
  have := certificate2209
  rw [h.1] at this
  norm_num at this
def C2210 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2210 : C2210.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2210 : ¬ (C2210.det = 0 ∧ ∀ i, C2210.adjugate i i ≠ 0) := by
  intro h
  have := certificate2210
  rw [h.1] at this
  norm_num at this
def C2211 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2211 : C2211.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2211 : ¬ (C2211.det = 0 ∧ ∀ i, C2211.adjugate i i ≠ 0) := by
  intro h
  have := certificate2211
  rw [h.1] at this
  norm_num at this
def C2212 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2212 : C2212.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2212 : ¬ (C2212.det = 0 ∧ ∀ i, C2212.adjugate i i ≠ 0) := by
  intro h
  have := certificate2212
  rw [h.1] at this
  norm_num at this
def C2213 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2213 : C2213.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2213 : ¬ (C2213.det = 0 ∧ ∀ i, C2213.adjugate i i ≠ 0) := by
  intro h
  have := certificate2213
  rw [h.1] at this
  norm_num at this
def C2214 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2214 : C2214.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2214 : ¬ (C2214.det = 0 ∧ ∀ i, C2214.adjugate i i ≠ 0) := by
  intro h
  have := certificate2214
  rw [h.1] at this
  norm_num at this
def C2215 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2215 : C2215.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2215 : ¬ (C2215.det = 0 ∧ ∀ i, C2215.adjugate i i ≠ 0) := by
  intro h
  have := certificate2215
  rw [h.1] at this
  norm_num at this
def C2216 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2216 : C2216.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2216 : ¬ (C2216.det = 0 ∧ ∀ i, C2216.adjugate i i ≠ 0) := by
  intro h
  have := certificate2216
  rw [h.1] at this
  norm_num at this
def C2217 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2217 : C2217.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2217 : ¬ (C2217.det = 0 ∧ ∀ i, C2217.adjugate i i ≠ 0) := by
  intro h
  have := certificate2217
  rw [h.1] at this
  norm_num at this
def C2218 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2218 : C2218.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2218 : ¬ (C2218.det = 0 ∧ ∀ i, C2218.adjugate i i ≠ 0) := by
  intro h
  have := certificate2218
  rw [h.1] at this
  norm_num at this
def C2219 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2219 : C2219.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2219 : ¬ (C2219.det = 0 ∧ ∀ i, C2219.adjugate i i ≠ 0) := by
  intro h
  have := certificate2219
  rw [h.1] at this
  norm_num at this
def C2220 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2220 : C2220.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2220 : ¬ (C2220.det = 0 ∧ ∀ i, C2220.adjugate i i ≠ 0) := by
  intro h
  have := certificate2220
  rw [h.1] at this
  norm_num at this
def C2221 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2221 : C2221.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2221 : ¬ (C2221.det = 0 ∧ ∀ i, C2221.adjugate i i ≠ 0) := by
  intro h
  have := certificate2221
  rw [h.1] at this
  norm_num at this
def C2222 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2222 : C2222.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2222 : ¬ (C2222.det = 0 ∧ ∀ i, C2222.adjugate i i ≠ 0) := by
  intro h
  have := certificate2222
  rw [h.1] at this
  norm_num at this
def C2223 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2223 : C2223.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2223 : ¬ (C2223.det = 0 ∧ ∀ i, C2223.adjugate i i ≠ 0) := by
  intro h
  have := certificate2223
  rw [h.1] at this
  norm_num at this
def C2224 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2224 : C2224.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2224 : ¬ (C2224.det = 0 ∧ ∀ i, C2224.adjugate i i ≠ 0) := by
  intro h
  have := certificate2224
  rw [h.1] at this
  norm_num at this
def C2225 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2225 : C2225.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2225 : ¬ (C2225.det = 0 ∧ ∀ i, C2225.adjugate i i ≠ 0) := by
  intro h
  have := certificate2225
  rw [h.1] at this
  norm_num at this
def C2226 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2226 : C2226.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2226 : ¬ (C2226.det = 0 ∧ ∀ i, C2226.adjugate i i ≠ 0) := by
  intro h
  have := certificate2226
  rw [h.1] at this
  norm_num at this
def C2227 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2227 : C2227.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2227 : ¬ (C2227.det = 0 ∧ ∀ i, C2227.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2227
def C2228 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2228 : C2228.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2228 : ¬ (C2228.det = 0 ∧ ∀ i, C2228.adjugate i i ≠ 0) := by
  intro h
  have := certificate2228
  rw [h.1] at this
  norm_num at this
def C2229 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2229 : C2229.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2229 : ¬ (C2229.det = 0 ∧ ∀ i, C2229.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2229
def C2230 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2230 : C2230.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2230 : ¬ (C2230.det = 0 ∧ ∀ i, C2230.adjugate i i ≠ 0) := by
  intro h
  have := certificate2230
  rw [h.1] at this
  norm_num at this
def C2231 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2231 : C2231.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2231 : ¬ (C2231.det = 0 ∧ ∀ i, C2231.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2231
def C2232 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2232 : C2232.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2232 : ¬ (C2232.det = 0 ∧ ∀ i, C2232.adjugate i i ≠ 0) := by
  intro h
  have := certificate2232
  rw [h.1] at this
  norm_num at this
def C2233 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2233 : C2233.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2233 : ¬ (C2233.det = 0 ∧ ∀ i, C2233.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2233
def C2234 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2234 : C2234.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2234 : ¬ (C2234.det = 0 ∧ ∀ i, C2234.adjugate i i ≠ 0) := by
  intro h
  have := certificate2234
  rw [h.1] at this
  norm_num at this
def C2235 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2235 : C2235.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2235 : ¬ (C2235.det = 0 ∧ ∀ i, C2235.adjugate i i ≠ 0) := by
  intro h
  have := certificate2235
  rw [h.1] at this
  norm_num at this
def C2236 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2236 : C2236.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2236 : ¬ (C2236.det = 0 ∧ ∀ i, C2236.adjugate i i ≠ 0) := by
  intro h
  have := certificate2236
  rw [h.1] at this
  norm_num at this
def C2237 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2237 : C2237.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2237 : ¬ (C2237.det = 0 ∧ ∀ i, C2237.adjugate i i ≠ 0) := by
  intro h
  have := certificate2237
  rw [h.1] at this
  norm_num at this
def C2238 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2238 : C2238.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2238 : ¬ (C2238.det = 0 ∧ ∀ i, C2238.adjugate i i ≠ 0) := by
  intro h
  have := certificate2238
  rw [h.1] at this
  norm_num at this
def C2239 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate2239 : C2239.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2239 : ¬ (C2239.det = 0 ∧ ∀ i, C2239.adjugate i i ≠ 0) := by
  intro h
  have := certificate2239
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0069
