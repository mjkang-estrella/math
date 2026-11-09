import VerifiedDet
namespace Nut8.NewCertificates0224
def C7168 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7168 : C7168.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7168 : ¬ (C7168.det = 0 ∧ ∀ i, C7168.adjugate i i ≠ 0) := by
  intro h
  have := certificate7168
  rw [h.1] at this
  norm_num at this
def C7169 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7169 : C7169.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7169 : ¬ (C7169.det = 0 ∧ ∀ i, C7169.adjugate i i ≠ 0) := by
  intro h
  have := certificate7169
  rw [h.1] at this
  norm_num at this
def C7170 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7170 : C7170.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7170 : ¬ (C7170.det = 0 ∧ ∀ i, C7170.adjugate i i ≠ 0) := by
  intro h
  have := certificate7170
  rw [h.1] at this
  norm_num at this
def C7171 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7171 : C7171.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7171 : ¬ (C7171.det = 0 ∧ ∀ i, C7171.adjugate i i ≠ 0) := by
  intro h
  have := certificate7171
  rw [h.1] at this
  norm_num at this
def C7172 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate7172 : C7172.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7172 : ¬ (C7172.det = 0 ∧ ∀ i, C7172.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7172
def C7173 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate7173 : C7173.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7173 : ¬ (C7173.det = 0 ∧ ∀ i, C7173.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7173
def C7174 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate7174 : C7174.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7174 : ¬ (C7174.det = 0 ∧ ∀ i, C7174.adjugate i i ≠ 0) := by
  intro h
  have := certificate7174
  rw [h.1] at this
  norm_num at this
def C7175 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate7175 : C7175.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7175 : ¬ (C7175.det = 0 ∧ ∀ i, C7175.adjugate i i ≠ 0) := by
  intro h
  have := certificate7175
  rw [h.1] at this
  norm_num at this
def C7176 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate7176 : C7176.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7176 : ¬ (C7176.det = 0 ∧ ∀ i, C7176.adjugate i i ≠ 0) := by
  intro h
  have := certificate7176
  rw [h.1] at this
  norm_num at this
def C7177 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate7177 : C7177.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7177 : ¬ (C7177.det = 0 ∧ ∀ i, C7177.adjugate i i ≠ 0) := by
  intro h
  have := certificate7177
  rw [h.1] at this
  norm_num at this
def C7178 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate7178 : C7178.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7178 : ¬ (C7178.det = 0 ∧ ∀ i, C7178.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7178
def C7179 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate7179 : C7179.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7179 : ¬ (C7179.det = 0 ∧ ∀ i, C7179.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7179
def C7180 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate7180 : C7180.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7180 : ¬ (C7180.det = 0 ∧ ∀ i, C7180.adjugate i i ≠ 0) := by
  intro h
  have := certificate7180
  rw [h.1] at this
  norm_num at this
def C7181 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate7181 : C7181.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7181 : ¬ (C7181.det = 0 ∧ ∀ i, C7181.adjugate i i ≠ 0) := by
  intro h
  have := certificate7181
  rw [h.1] at this
  norm_num at this
def C7182 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate7182 : C7182.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7182 : ¬ (C7182.det = 0 ∧ ∀ i, C7182.adjugate i i ≠ 0) := by
  intro h
  have := certificate7182
  rw [h.1] at this
  norm_num at this
def C7183 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate7183 : C7183.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7183 : ¬ (C7183.det = 0 ∧ ∀ i, C7183.adjugate i i ≠ 0) := by
  intro h
  have := certificate7183
  rw [h.1] at this
  norm_num at this
def C7184 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate7184 : C7184.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7184 : ¬ (C7184.det = 0 ∧ ∀ i, C7184.adjugate i i ≠ 0) := by
  intro h
  have := certificate7184
  rw [h.1] at this
  norm_num at this
def C7185 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate7185 : C7185.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7185 : ¬ (C7185.det = 0 ∧ ∀ i, C7185.adjugate i i ≠ 0) := by
  intro h
  have := certificate7185
  rw [h.1] at this
  norm_num at this
def C7186 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate7186 : C7186.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7186 : ¬ (C7186.det = 0 ∧ ∀ i, C7186.adjugate i i ≠ 0) := by
  intro h
  have := certificate7186
  rw [h.1] at this
  norm_num at this
def C7187 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate7187 : C7187.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7187 : ¬ (C7187.det = 0 ∧ ∀ i, C7187.adjugate i i ≠ 0) := by
  intro h
  have := certificate7187
  rw [h.1] at this
  norm_num at this
def C7188 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7188 : C7188.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7188 : ¬ (C7188.det = 0 ∧ ∀ i, C7188.adjugate i i ≠ 0) := by
  intro h
  have := certificate7188
  rw [h.1] at this
  norm_num at this
def C7189 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7189 : C7189.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7189 : ¬ (C7189.det = 0 ∧ ∀ i, C7189.adjugate i i ≠ 0) := by
  intro h
  have := certificate7189
  rw [h.1] at this
  norm_num at this
def C7190 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7190 : C7190.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7190 : ¬ (C7190.det = 0 ∧ ∀ i, C7190.adjugate i i ≠ 0) := by
  intro h
  have := certificate7190
  rw [h.1] at this
  norm_num at this
def C7191 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7191 : C7191.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7191 : ¬ (C7191.det = 0 ∧ ∀ i, C7191.adjugate i i ≠ 0) := by
  intro h
  have := certificate7191
  rw [h.1] at this
  norm_num at this
def C7192 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7192 : C7192.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7192 : ¬ (C7192.det = 0 ∧ ∀ i, C7192.adjugate i i ≠ 0) := by
  intro h
  have := certificate7192
  rw [h.1] at this
  norm_num at this
def C7193 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7193 : C7193.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7193 : ¬ (C7193.det = 0 ∧ ∀ i, C7193.adjugate i i ≠ 0) := by
  intro h
  have := certificate7193
  rw [h.1] at this
  norm_num at this
def C7194 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7194 : C7194.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7194 : ¬ (C7194.det = 0 ∧ ∀ i, C7194.adjugate i i ≠ 0) := by
  intro h
  have := certificate7194
  rw [h.1] at this
  norm_num at this
def C7195 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7195 : C7195.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7195 : ¬ (C7195.det = 0 ∧ ∀ i, C7195.adjugate i i ≠ 0) := by
  intro h
  have := certificate7195
  rw [h.1] at this
  norm_num at this
def C7196 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7196 : C7196.det = (144 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7196 : ¬ (C7196.det = 0 ∧ ∀ i, C7196.adjugate i i ≠ 0) := by
  intro h
  have := certificate7196
  rw [h.1] at this
  norm_num at this
def C7197 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7197 : C7197.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7197 : ¬ (C7197.det = 0 ∧ ∀ i, C7197.adjugate i i ≠ 0) := by
  intro h
  have := certificate7197
  rw [h.1] at this
  norm_num at this
def C7198 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7198 : C7198.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7198 : ¬ (C7198.det = 0 ∧ ∀ i, C7198.adjugate i i ≠ 0) := by
  intro h
  have := certificate7198
  rw [h.1] at this
  norm_num at this
def C7199 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7199 : C7199.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7199 : ¬ (C7199.det = 0 ∧ ∀ i, C7199.adjugate i i ≠ 0) := by
  intro h
  have := certificate7199
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0224
