import VerifiedDet
namespace Nut8.NewCertificates0225
def C7200 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7200 : C7200.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7200 : ¬ (C7200.det = 0 ∧ ∀ i, C7200.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7200
def C7201 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7201 : C7201.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7201 : ¬ (C7201.det = 0 ∧ ∀ i, C7201.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7201
def C7202 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7202 : C7202.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7202 : ¬ (C7202.det = 0 ∧ ∀ i, C7202.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7202
def C7203 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7203 : C7203.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7203 : ¬ (C7203.det = 0 ∧ ∀ i, C7203.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7203
def C7204 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7204 : C7204.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7204 : ¬ (C7204.det = 0 ∧ ∀ i, C7204.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7204
def C7205 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7205 : C7205.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7205 : ¬ (C7205.det = 0 ∧ ∀ i, C7205.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7205
def C7206 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7206 : C7206.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7206 : ¬ (C7206.det = 0 ∧ ∀ i, C7206.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7206
def C7207 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7207 : C7207.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7207 : ¬ (C7207.det = 0 ∧ ∀ i, C7207.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7207
def C7208 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7208 : C7208.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7208 : ¬ (C7208.det = 0 ∧ ∀ i, C7208.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7208
def C7209 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7209 : C7209.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7209 : ¬ (C7209.det = 0 ∧ ∀ i, C7209.adjugate i i ≠ 0) := by
  intro h
  have := certificate7209
  rw [h.1] at this
  norm_num at this
def C7210 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7210 : C7210.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7210 : ¬ (C7210.det = 0 ∧ ∀ i, C7210.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7210
def C7211 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7211 : C7211.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7211 : ¬ (C7211.det = 0 ∧ ∀ i, C7211.adjugate i i ≠ 0) := by
  intro h
  have := certificate7211
  rw [h.1] at this
  norm_num at this
def C7212 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7212 : C7212.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7212 : ¬ (C7212.det = 0 ∧ ∀ i, C7212.adjugate i i ≠ 0) := by
  intro h
  have := certificate7212
  rw [h.1] at this
  norm_num at this
def C7213 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7213 : C7213.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7213 : ¬ (C7213.det = 0 ∧ ∀ i, C7213.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7213
def C7214 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7214 : C7214.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7214 : ¬ (C7214.det = 0 ∧ ∀ i, C7214.adjugate i i ≠ 0) := by
  intro h
  have := certificate7214
  rw [h.1] at this
  norm_num at this
def C7215 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7215 : C7215.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7215 : ¬ (C7215.det = 0 ∧ ∀ i, C7215.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7215
def C7216 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7216 : C7216.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7216 : ¬ (C7216.det = 0 ∧ ∀ i, C7216.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7216
def C7217 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7217 : C7217.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7217 : ¬ (C7217.det = 0 ∧ ∀ i, C7217.adjugate i i ≠ 0) := by
  intro h
  have := certificate7217
  rw [h.1] at this
  norm_num at this
def C7218 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7218 : C7218.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7218 : ¬ (C7218.det = 0 ∧ ∀ i, C7218.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7218
def C7219 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7219 : C7219.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7219 : ¬ (C7219.det = 0 ∧ ∀ i, C7219.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7219
def C7220 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7220 : C7220.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7220 : ¬ (C7220.det = 0 ∧ ∀ i, C7220.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7220
def C7221 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7221 : C7221.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7221 : ¬ (C7221.det = 0 ∧ ∀ i, C7221.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7221
def C7222 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7222 : C7222.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7222 : ¬ (C7222.det = 0 ∧ ∀ i, C7222.adjugate i i ≠ 0) := by
  intro h
  have := certificate7222
  rw [h.1] at this
  norm_num at this
def C7223 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7223 : C7223.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7223 : ¬ (C7223.det = 0 ∧ ∀ i, C7223.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7223
def C7224 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7224 : C7224.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7224 : ¬ (C7224.det = 0 ∧ ∀ i, C7224.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7224
def C7225 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7225 : C7225.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7225 : ¬ (C7225.det = 0 ∧ ∀ i, C7225.adjugate i i ≠ 0) := by
  intro h
  have := certificate7225
  rw [h.1] at this
  norm_num at this
def C7226 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7226 : C7226.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7226 : ¬ (C7226.det = 0 ∧ ∀ i, C7226.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7226
def C7227 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7227 : C7227.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7227 : ¬ (C7227.det = 0 ∧ ∀ i, C7227.adjugate i i ≠ 0) := by
  intro h
  have := certificate7227
  rw [h.1] at this
  norm_num at this
def C7228 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7228 : C7228.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7228 : ¬ (C7228.det = 0 ∧ ∀ i, C7228.adjugate i i ≠ 0) := by
  intro h
  have := certificate7228
  rw [h.1] at this
  norm_num at this
def C7229 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7229 : C7229.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7229 : ¬ (C7229.det = 0 ∧ ∀ i, C7229.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7229
def C7230 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7230 : C7230.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7230 : ¬ (C7230.det = 0 ∧ ∀ i, C7230.adjugate i i ≠ 0) := by
  intro h
  have := certificate7230
  rw [h.1] at this
  norm_num at this
def C7231 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7231 : C7231.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7231 : ¬ (C7231.det = 0 ∧ ∀ i, C7231.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7231
end Nut8.NewCertificates0225
