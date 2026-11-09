import VerifiedDet
namespace Nut8.NewCertificates0130
def C4160 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate4160 : C4160.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4160 : ¬ (C4160.det = 0 ∧ ∀ i, C4160.adjugate i i ≠ 0) := by
  intro h
  have := certificate4160
  rw [h.1] at this
  norm_num at this
def C4161 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate4161 : C4161.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4161 : ¬ (C4161.det = 0 ∧ ∀ i, C4161.adjugate i i ≠ 0) := by
  intro h
  have := certificate4161
  rw [h.1] at this
  norm_num at this
def C4162 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate4162 : C4162.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4162 : ¬ (C4162.det = 0 ∧ ∀ i, C4162.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4162
def C4163 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate4163 : C4163.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4163 : ¬ (C4163.det = 0 ∧ ∀ i, C4163.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4163
def C4164 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate4164 : C4164.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4164 : ¬ (C4164.det = 0 ∧ ∀ i, C4164.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4164
def C4165 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate4165 : C4165.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4165 : ¬ (C4165.det = 0 ∧ ∀ i, C4165.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4165
def C4166 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate4166 : C4166.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4166 : ¬ (C4166.det = 0 ∧ ∀ i, C4166.adjugate i i ≠ 0) := by
  intro h
  have := certificate4166
  rw [h.1] at this
  norm_num at this
def C4167 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate4167 : C4167.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4167 : ¬ (C4167.det = 0 ∧ ∀ i, C4167.adjugate i i ≠ 0) := by
  intro h
  have := certificate4167
  rw [h.1] at this
  norm_num at this
def C4168 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate4168 : C4168.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4168 : ¬ (C4168.det = 0 ∧ ∀ i, C4168.adjugate i i ≠ 0) := by
  intro h
  have := certificate4168
  rw [h.1] at this
  norm_num at this
def C4169 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate4169 : C4169.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4169 : ¬ (C4169.det = 0 ∧ ∀ i, C4169.adjugate i i ≠ 0) := by
  intro h
  have := certificate4169
  rw [h.1] at this
  norm_num at this
def C4170 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate4170 : C4170.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4170 : ¬ (C4170.det = 0 ∧ ∀ i, C4170.adjugate i i ≠ 0) := by
  intro h
  have := certificate4170
  rw [h.1] at this
  norm_num at this
def C4171 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate4171 : C4171.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4171 : ¬ (C4171.det = 0 ∧ ∀ i, C4171.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4171
def C4172 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate4172 : C4172.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4172 : ¬ (C4172.det = 0 ∧ ∀ i, C4172.adjugate i i ≠ 0) := by
  intro h
  have := certificate4172
  rw [h.1] at this
  norm_num at this
def C4173 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate4173 : C4173.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4173 : ¬ (C4173.det = 0 ∧ ∀ i, C4173.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4173
def C4174 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate4174 : C4174.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4174 : ¬ (C4174.det = 0 ∧ ∀ i, C4174.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4174
def C4175 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate4175 : C4175.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4175 : ¬ (C4175.det = 0 ∧ ∀ i, C4175.adjugate i i ≠ 0) := by
  intro h
  have := certificate4175
  rw [h.1] at this
  norm_num at this
def C4176 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate4176 : C4176.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4176 : ¬ (C4176.det = 0 ∧ ∀ i, C4176.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4176
def C4177 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate4177 : C4177.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4177 : ¬ (C4177.det = 0 ∧ ∀ i, C4177.adjugate i i ≠ 0) := by
  intro h
  have := certificate4177
  rw [h.1] at this
  norm_num at this
def C4178 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate4178 : C4178.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4178 : ¬ (C4178.det = 0 ∧ ∀ i, C4178.adjugate i i ≠ 0) := by
  intro h
  have := certificate4178
  rw [h.1] at this
  norm_num at this
def C4179 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate4179 : C4179.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4179 : ¬ (C4179.det = 0 ∧ ∀ i, C4179.adjugate i i ≠ 0) := by
  intro h
  have := certificate4179
  rw [h.1] at this
  norm_num at this
def C4180 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate4180 : C4180.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4180 : ¬ (C4180.det = 0 ∧ ∀ i, C4180.adjugate i i ≠ 0) := by
  intro h
  have := certificate4180
  rw [h.1] at this
  norm_num at this
def C4181 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate4181 : C4181.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4181 : ¬ (C4181.det = 0 ∧ ∀ i, C4181.adjugate i i ≠ 0) := by
  intro h
  have := certificate4181
  rw [h.1] at this
  norm_num at this
def C4182 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4182 : C4182.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4182 : ¬ (C4182.det = 0 ∧ ∀ i, C4182.adjugate i i ≠ 0) := by
  intro h
  have := certificate4182
  rw [h.1] at this
  norm_num at this
def C4183 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4183 : C4183.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4183 : ¬ (C4183.det = 0 ∧ ∀ i, C4183.adjugate i i ≠ 0) := by
  intro h
  have := certificate4183
  rw [h.1] at this
  norm_num at this
def C4184 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4184 : C4184.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4184 : ¬ (C4184.det = 0 ∧ ∀ i, C4184.adjugate i i ≠ 0) := by
  intro h
  have := certificate4184
  rw [h.1] at this
  norm_num at this
def C4185 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4185 : C4185.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4185 : ¬ (C4185.det = 0 ∧ ∀ i, C4185.adjugate i i ≠ 0) := by
  intro h
  have := certificate4185
  rw [h.1] at this
  norm_num at this
def C4186 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4186 : C4186.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4186 : ¬ (C4186.det = 0 ∧ ∀ i, C4186.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4186
def C4187 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4187 : C4187.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4187 : ¬ (C4187.det = 0 ∧ ∀ i, C4187.adjugate i i ≠ 0) := by
  intro h
  have := certificate4187
  rw [h.1] at this
  norm_num at this
def C4188 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4188 : C4188.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4188 : ¬ (C4188.det = 0 ∧ ∀ i, C4188.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4188
def C4189 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate4189 : C4189.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4189 : ¬ (C4189.det = 0 ∧ ∀ i, C4189.adjugate i i ≠ 0) := by
  intro h
  have := certificate4189
  rw [h.1] at this
  norm_num at this
def C4190 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4190 : C4190.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4190 : ¬ (C4190.det = 0 ∧ ∀ i, C4190.adjugate i i ≠ 0) := by
  intro h
  have := certificate4190
  rw [h.1] at this
  norm_num at this
def C4191 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate4191 : C4191.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4191 : ¬ (C4191.det = 0 ∧ ∀ i, C4191.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4191
end Nut8.NewCertificates0130
