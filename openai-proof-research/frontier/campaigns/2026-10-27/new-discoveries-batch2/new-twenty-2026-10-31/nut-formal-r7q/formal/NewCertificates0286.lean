import VerifiedDet
namespace Nut8.NewCertificates0286
def C9152 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9152 : C9152.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9152 : ¬ (C9152.det = 0 ∧ ∀ i, C9152.adjugate i i ≠ 0) := by
  intro h
  have := certificate9152
  rw [h.1] at this
  norm_num at this
def C9153 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9153 : C9153.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9153 : ¬ (C9153.det = 0 ∧ ∀ i, C9153.adjugate i i ≠ 0) := by
  intro h
  have := certificate9153
  rw [h.1] at this
  norm_num at this
def C9154 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9154 : C9154.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9154 : ¬ (C9154.det = 0 ∧ ∀ i, C9154.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9154
def C9155 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9155 : C9155.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9155 : ¬ (C9155.det = 0 ∧ ∀ i, C9155.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9155
def C9156 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9156 : C9156.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9156 : ¬ (C9156.det = 0 ∧ ∀ i, C9156.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9156
def C9157 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9157 : C9157.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9157 : ¬ (C9157.det = 0 ∧ ∀ i, C9157.adjugate i i ≠ 0) := by
  intro h
  have := certificate9157
  rw [h.1] at this
  norm_num at this
def C9158 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9158 : C9158.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9158 : ¬ (C9158.det = 0 ∧ ∀ i, C9158.adjugate i i ≠ 0) := by
  intro h
  have := certificate9158
  rw [h.1] at this
  norm_num at this
def C9159 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9159 : C9159.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9159 : ¬ (C9159.det = 0 ∧ ∀ i, C9159.adjugate i i ≠ 0) := by
  intro h
  have := certificate9159
  rw [h.1] at this
  norm_num at this
def C9160 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9160 : C9160.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9160 : ¬ (C9160.det = 0 ∧ ∀ i, C9160.adjugate i i ≠ 0) := by
  intro h
  have := certificate9160
  rw [h.1] at this
  norm_num at this
def C9161 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9161 : C9161.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9161 : ¬ (C9161.det = 0 ∧ ∀ i, C9161.adjugate i i ≠ 0) := by
  intro h
  have := certificate9161
  rw [h.1] at this
  norm_num at this
def C9162 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9162 : C9162.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9162 : ¬ (C9162.det = 0 ∧ ∀ i, C9162.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9162
def C9163 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9163 : C9163.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9163 : ¬ (C9163.det = 0 ∧ ∀ i, C9163.adjugate i i ≠ 0) := by
  intro h
  have := certificate9163
  rw [h.1] at this
  norm_num at this
def C9164 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9164 : C9164.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9164 : ¬ (C9164.det = 0 ∧ ∀ i, C9164.adjugate i i ≠ 0) := by
  intro h
  have := certificate9164
  rw [h.1] at this
  norm_num at this
def C9165 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9165 : C9165.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9165 : ¬ (C9165.det = 0 ∧ ∀ i, C9165.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9165
def C9166 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9166 : C9166.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9166 : ¬ (C9166.det = 0 ∧ ∀ i, C9166.adjugate i i ≠ 0) := by
  intro h
  have := certificate9166
  rw [h.1] at this
  norm_num at this
def C9167 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9167 : C9167.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9167 : ¬ (C9167.det = 0 ∧ ∀ i, C9167.adjugate i i ≠ 0) := by
  intro h
  have := certificate9167
  rw [h.1] at this
  norm_num at this
def C9168 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9168 : C9168.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9168 : ¬ (C9168.det = 0 ∧ ∀ i, C9168.adjugate i i ≠ 0) := by
  intro h
  have := certificate9168
  rw [h.1] at this
  norm_num at this
def C9169 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9169 : C9169.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9169 : ¬ (C9169.det = 0 ∧ ∀ i, C9169.adjugate i i ≠ 0) := by
  intro h
  have := certificate9169
  rw [h.1] at this
  norm_num at this
def C9170 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9170 : C9170.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9170 : ¬ (C9170.det = 0 ∧ ∀ i, C9170.adjugate i i ≠ 0) := by
  intro h
  have := certificate9170
  rw [h.1] at this
  norm_num at this
def C9171 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9171 : C9171.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9171 : ¬ (C9171.det = 0 ∧ ∀ i, C9171.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9171
end Nut8.NewCertificates0286
