import VerifiedDet
namespace Nut8.NewCertificates0131
def C4192 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4192 : C4192.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4192 : ¬ (C4192.det = 0 ∧ ∀ i, C4192.adjugate i i ≠ 0) := by
  intro h
  have := certificate4192
  rw [h.1] at this
  norm_num at this
def C4193 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4193 : C4193.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4193 : ¬ (C4193.det = 0 ∧ ∀ i, C4193.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4193
def C4194 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4194 : C4194.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4194 : ¬ (C4194.det = 0 ∧ ∀ i, C4194.adjugate i i ≠ 0) := by
  intro h
  have := certificate4194
  rw [h.1] at this
  norm_num at this
def C4195 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4195 : C4195.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4195 : ¬ (C4195.det = 0 ∧ ∀ i, C4195.adjugate i i ≠ 0) := by
  intro h
  have := certificate4195
  rw [h.1] at this
  norm_num at this
def C4196 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4196 : C4196.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4196 : ¬ (C4196.det = 0 ∧ ∀ i, C4196.adjugate i i ≠ 0) := by
  intro h
  have := certificate4196
  rw [h.1] at this
  norm_num at this
def C4197 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4197 : C4197.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4197 : ¬ (C4197.det = 0 ∧ ∀ i, C4197.adjugate i i ≠ 0) := by
  intro h
  have := certificate4197
  rw [h.1] at this
  norm_num at this
def C4198 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4198 : C4198.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4198 : ¬ (C4198.det = 0 ∧ ∀ i, C4198.adjugate i i ≠ 0) := by
  intro h
  have := certificate4198
  rw [h.1] at this
  norm_num at this
def C4199 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4199 : C4199.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4199 : ¬ (C4199.det = 0 ∧ ∀ i, C4199.adjugate i i ≠ 0) := by
  intro h
  have := certificate4199
  rw [h.1] at this
  norm_num at this
def C4200 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4200 : C4200.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4200 : ¬ (C4200.det = 0 ∧ ∀ i, C4200.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4200
def C4201 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4201 : C4201.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4201 : ¬ (C4201.det = 0 ∧ ∀ i, C4201.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4201
def C4202 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4202 : C4202.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4202 : ¬ (C4202.det = 0 ∧ ∀ i, C4202.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4202
def C4203 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4203 : C4203.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4203 : ¬ (C4203.det = 0 ∧ ∀ i, C4203.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4203
def C4204 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4204 : C4204.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4204 : ¬ (C4204.det = 0 ∧ ∀ i, C4204.adjugate i i ≠ 0) := by
  intro h
  have := certificate4204
  rw [h.1] at this
  norm_num at this
def C4205 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4205 : C4205.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4205 : ¬ (C4205.det = 0 ∧ ∀ i, C4205.adjugate i i ≠ 0) := by
  intro h
  have := certificate4205
  rw [h.1] at this
  norm_num at this
def C4206 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate4206 : C4206.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4206 : ¬ (C4206.det = 0 ∧ ∀ i, C4206.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4206
def C4207 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate4207 : C4207.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4207 : ¬ (C4207.det = 0 ∧ ∀ i, C4207.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4207
def C4208 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate4208 : C4208.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4208 : ¬ (C4208.det = 0 ∧ ∀ i, C4208.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4208
def C4209 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate4209 : C4209.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4209 : ¬ (C4209.det = 0 ∧ ∀ i, C4209.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4209
def C4210 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate4210 : C4210.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4210 : ¬ (C4210.det = 0 ∧ ∀ i, C4210.adjugate i i ≠ 0) := by
  intro h
  have := certificate4210
  rw [h.1] at this
  norm_num at this
def C4211 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate4211 : C4211.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4211 : ¬ (C4211.det = 0 ∧ ∀ i, C4211.adjugate i i ≠ 0) := by
  intro h
  have := certificate4211
  rw [h.1] at this
  norm_num at this
def C4212 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate4212 : C4212.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4212 : ¬ (C4212.det = 0 ∧ ∀ i, C4212.adjugate i i ≠ 0) := by
  intro h
  have := certificate4212
  rw [h.1] at this
  norm_num at this
def C4213 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate4213 : C4213.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4213 : ¬ (C4213.det = 0 ∧ ∀ i, C4213.adjugate i i ≠ 0) := by
  intro h
  have := certificate4213
  rw [h.1] at this
  norm_num at this
def C4214 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate4214 : C4214.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4214 : ¬ (C4214.det = 0 ∧ ∀ i, C4214.adjugate i i ≠ 0) := by
  intro h
  have := certificate4214
  rw [h.1] at this
  norm_num at this
def C4215 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate4215 : C4215.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4215 : ¬ (C4215.det = 0 ∧ ∀ i, C4215.adjugate i i ≠ 0) := by
  intro h
  have := certificate4215
  rw [h.1] at this
  norm_num at this
def C4216 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate4216 : C4216.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4216 : ¬ (C4216.det = 0 ∧ ∀ i, C4216.adjugate i i ≠ 0) := by
  intro h
  have := certificate4216
  rw [h.1] at this
  norm_num at this
def C4217 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate4217 : C4217.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4217 : ¬ (C4217.det = 0 ∧ ∀ i, C4217.adjugate i i ≠ 0) := by
  intro h
  have := certificate4217
  rw [h.1] at this
  norm_num at this
def C4218 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate4218 : C4218.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4218 : ¬ (C4218.det = 0 ∧ ∀ i, C4218.adjugate i i ≠ 0) := by
  intro h
  have := certificate4218
  rw [h.1] at this
  norm_num at this
def C4219 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate4219 : C4219.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4219 : ¬ (C4219.det = 0 ∧ ∀ i, C4219.adjugate i i ≠ 0) := by
  intro h
  have := certificate4219
  rw [h.1] at this
  norm_num at this
def C4220 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate4220 : C4220.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4220 : ¬ (C4220.det = 0 ∧ ∀ i, C4220.adjugate i i ≠ 0) := by
  intro h
  have := certificate4220
  rw [h.1] at this
  norm_num at this
def C4221 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate4221 : C4221.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4221 : ¬ (C4221.det = 0 ∧ ∀ i, C4221.adjugate i i ≠ 0) := by
  intro h
  have := certificate4221
  rw [h.1] at this
  norm_num at this
def C4222 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate4222 : C4222.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4222 : ¬ (C4222.det = 0 ∧ ∀ i, C4222.adjugate i i ≠ 0) := by
  intro h
  have := certificate4222
  rw [h.1] at this
  norm_num at this
def C4223 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate4223 : C4223.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4223 : ¬ (C4223.det = 0 ∧ ∀ i, C4223.adjugate i i ≠ 0) := by
  intro h
  have := certificate4223
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0131
