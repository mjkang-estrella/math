import VerifiedDet
namespace Nut8.NewCertificates0100
def C3200 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3200 : C3200.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3200 : ¬ (C3200.det = 0 ∧ ∀ i, C3200.adjugate i i ≠ 0) := by
  intro h
  have := certificate3200
  rw [h.1] at this
  norm_num at this
def C3201 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3201 : C3201.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3201 : ¬ (C3201.det = 0 ∧ ∀ i, C3201.adjugate i i ≠ 0) := by
  intro h
  have := certificate3201
  rw [h.1] at this
  norm_num at this
def C3202 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3202 : C3202.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3202 : ¬ (C3202.det = 0 ∧ ∀ i, C3202.adjugate i i ≠ 0) := by
  intro h
  have := certificate3202
  rw [h.1] at this
  norm_num at this
def C3203 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3203 : C3203.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3203 : ¬ (C3203.det = 0 ∧ ∀ i, C3203.adjugate i i ≠ 0) := by
  intro h
  have := certificate3203
  rw [h.1] at this
  norm_num at this
def C3204 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3204 : C3204.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3204 : ¬ (C3204.det = 0 ∧ ∀ i, C3204.adjugate i i ≠ 0) := by
  intro h
  have := certificate3204
  rw [h.1] at this
  norm_num at this
def C3205 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3205 : C3205.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3205 : ¬ (C3205.det = 0 ∧ ∀ i, C3205.adjugate i i ≠ 0) := by
  intro h
  have := certificate3205
  rw [h.1] at this
  norm_num at this
def C3206 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate3206 : C3206.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3206 : ¬ (C3206.det = 0 ∧ ∀ i, C3206.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3206
def C3207 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate3207 : C3207.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3207 : ¬ (C3207.det = 0 ∧ ∀ i, C3207.adjugate i i ≠ 0) := by
  intro h
  have := certificate3207
  rw [h.1] at this
  norm_num at this
def C3208 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate3208 : C3208.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3208 : ¬ (C3208.det = 0 ∧ ∀ i, C3208.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3208
def C3209 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate3209 : C3209.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3209 : ¬ (C3209.det = 0 ∧ ∀ i, C3209.adjugate i i ≠ 0) := by
  intro h
  have := certificate3209
  rw [h.1] at this
  norm_num at this
def C3210 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate3210 : C3210.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3210 : ¬ (C3210.det = 0 ∧ ∀ i, C3210.adjugate i i ≠ 0) := by
  intro h
  have := certificate3210
  rw [h.1] at this
  norm_num at this
def C3211 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate3211 : C3211.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3211 : ¬ (C3211.det = 0 ∧ ∀ i, C3211.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3211
def C3212 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate3212 : C3212.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3212 : ¬ (C3212.det = 0 ∧ ∀ i, C3212.adjugate i i ≠ 0) := by
  intro h
  have := certificate3212
  rw [h.1] at this
  norm_num at this
def C3213 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate3213 : C3213.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3213 : ¬ (C3213.det = 0 ∧ ∀ i, C3213.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3213
def C3214 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate3214 : C3214.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3214 : ¬ (C3214.det = 0 ∧ ∀ i, C3214.adjugate i i ≠ 0) := by
  intro h
  have := certificate3214
  rw [h.1] at this
  norm_num at this
def C3215 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate3215 : C3215.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3215 : ¬ (C3215.det = 0 ∧ ∀ i, C3215.adjugate i i ≠ 0) := by
  intro h
  have := certificate3215
  rw [h.1] at this
  norm_num at this
def C3216 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate3216 : C3216.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3216 : ¬ (C3216.det = 0 ∧ ∀ i, C3216.adjugate i i ≠ 0) := by
  intro h
  have := certificate3216
  rw [h.1] at this
  norm_num at this
def C3217 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate3217 : C3217.det = (-92 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3217 : ¬ (C3217.det = 0 ∧ ∀ i, C3217.adjugate i i ≠ 0) := by
  intro h
  have := certificate3217
  rw [h.1] at this
  norm_num at this
def C3218 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate3218 : C3218.det = (-92 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3218 : ¬ (C3218.det = 0 ∧ ∀ i, C3218.adjugate i i ≠ 0) := by
  intro h
  have := certificate3218
  rw [h.1] at this
  norm_num at this
def C3219 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate3219 : C3219.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3219 : ¬ (C3219.det = 0 ∧ ∀ i, C3219.adjugate i i ≠ 0) := by
  intro h
  have := certificate3219
  rw [h.1] at this
  norm_num at this
def C3220 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate3220 : C3220.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3220 : ¬ (C3220.det = 0 ∧ ∀ i, C3220.adjugate i i ≠ 0) := by
  intro h
  have := certificate3220
  rw [h.1] at this
  norm_num at this
def C3221 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate3221 : C3221.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3221 : ¬ (C3221.det = 0 ∧ ∀ i, C3221.adjugate i i ≠ 0) := by
  intro h
  have := certificate3221
  rw [h.1] at this
  norm_num at this
def C3222 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3222 : C3222.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3222 : ¬ (C3222.det = 0 ∧ ∀ i, C3222.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3222
def C3223 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3223 : C3223.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3223 : ¬ (C3223.det = 0 ∧ ∀ i, C3223.adjugate i i ≠ 0) := by
  intro h
  have := certificate3223
  rw [h.1] at this
  norm_num at this
def C3224 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3224 : C3224.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3224 : ¬ (C3224.det = 0 ∧ ∀ i, C3224.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3224
def C3225 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3225 : C3225.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3225 : ¬ (C3225.det = 0 ∧ ∀ i, C3225.adjugate i i ≠ 0) := by
  intro h
  have := certificate3225
  rw [h.1] at this
  norm_num at this
def C3226 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3226 : C3226.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3226 : ¬ (C3226.det = 0 ∧ ∀ i, C3226.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3226
def C3227 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3227 : C3227.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3227 : ¬ (C3227.det = 0 ∧ ∀ i, C3227.adjugate i i ≠ 0) := by
  intro h
  have := certificate3227
  rw [h.1] at this
  norm_num at this
def C3228 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3228 : C3228.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3228 : ¬ (C3228.det = 0 ∧ ∀ i, C3228.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3228
def C3229 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0, 0, -2]
theorem certificate3229 : C3229.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3229 : ¬ (C3229.det = 0 ∧ ∀ i, C3229.adjugate i i ≠ 0) := by
  intro h
  have := certificate3229
  rw [h.1] at this
  norm_num at this
def C3230 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3230 : C3230.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3230 : ¬ (C3230.det = 0 ∧ ∀ i, C3230.adjugate i i ≠ 0) := by
  intro h
  have := certificate3230
  rw [h.1] at this
  norm_num at this
def C3231 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 0, 0, 2]
theorem certificate3231 : C3231.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3231 : ¬ (C3231.det = 0 ∧ ∀ i, C3231.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3231
end Nut8.NewCertificates0100
