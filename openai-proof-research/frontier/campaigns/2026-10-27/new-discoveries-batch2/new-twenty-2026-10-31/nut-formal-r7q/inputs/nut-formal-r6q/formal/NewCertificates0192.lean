import VerifiedDet
namespace Nut8.NewCertificates0192
def C6144 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate6144 : C6144.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6144 : ¬ (C6144.det = 0 ∧ ∀ i, C6144.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6144
def C6145 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate6145 : C6145.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6145 : ¬ (C6145.det = 0 ∧ ∀ i, C6145.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6145
def C6146 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate6146 : C6146.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6146 : ¬ (C6146.det = 0 ∧ ∀ i, C6146.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6146
def C6147 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate6147 : C6147.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6147 : ¬ (C6147.det = 0 ∧ ∀ i, C6147.adjugate i i ≠ 0) := by
  intro h
  have := certificate6147
  rw [h.1] at this
  norm_num at this
def C6148 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate6148 : C6148.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6148 : ¬ (C6148.det = 0 ∧ ∀ i, C6148.adjugate i i ≠ 0) := by
  intro h
  have := certificate6148
  rw [h.1] at this
  norm_num at this
def C6149 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate6149 : C6149.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6149 : ¬ (C6149.det = 0 ∧ ∀ i, C6149.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6149
def C6150 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate6150 : C6150.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6150 : ¬ (C6150.det = 0 ∧ ∀ i, C6150.adjugate i i ≠ 0) := by
  intro h
  have := certificate6150
  rw [h.1] at this
  norm_num at this
def C6151 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate6151 : C6151.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6151 : ¬ (C6151.det = 0 ∧ ∀ i, C6151.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6151
def C6152 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate6152 : C6152.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6152 : ¬ (C6152.det = 0 ∧ ∀ i, C6152.adjugate i i ≠ 0) := by
  intro h
  have := certificate6152
  rw [h.1] at this
  norm_num at this
def C6153 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate6153 : C6153.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6153 : ¬ (C6153.det = 0 ∧ ∀ i, C6153.adjugate i i ≠ 0) := by
  intro h
  have := certificate6153
  rw [h.1] at this
  norm_num at this
def C6154 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate6154 : C6154.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6154 : ¬ (C6154.det = 0 ∧ ∀ i, C6154.adjugate i i ≠ 0) := by
  intro h
  have := certificate6154
  rw [h.1] at this
  norm_num at this
def C6155 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate6155 : C6155.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6155 : ¬ (C6155.det = 0 ∧ ∀ i, C6155.adjugate i i ≠ 0) := by
  intro h
  have := certificate6155
  rw [h.1] at this
  norm_num at this
def C6156 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate6156 : C6156.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6156 : ¬ (C6156.det = 0 ∧ ∀ i, C6156.adjugate i i ≠ 0) := by
  intro h
  have := certificate6156
  rw [h.1] at this
  norm_num at this
def C6157 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate6157 : C6157.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6157 : ¬ (C6157.det = 0 ∧ ∀ i, C6157.adjugate i i ≠ 0) := by
  intro h
  have := certificate6157
  rw [h.1] at this
  norm_num at this
def C6158 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate6158 : C6158.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6158 : ¬ (C6158.det = 0 ∧ ∀ i, C6158.adjugate i i ≠ 0) := by
  intro h
  have := certificate6158
  rw [h.1] at this
  norm_num at this
def C6159 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate6159 : C6159.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6159 : ¬ (C6159.det = 0 ∧ ∀ i, C6159.adjugate i i ≠ 0) := by
  intro h
  have := certificate6159
  rw [h.1] at this
  norm_num at this
def C6160 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate6160 : C6160.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6160 : ¬ (C6160.det = 0 ∧ ∀ i, C6160.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6160
def C6161 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate6161 : C6161.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6161 : ¬ (C6161.det = 0 ∧ ∀ i, C6161.adjugate i i ≠ 0) := by
  intro h
  have := certificate6161
  rw [h.1] at this
  norm_num at this
def C6162 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate6162 : C6162.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6162 : ¬ (C6162.det = 0 ∧ ∀ i, C6162.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6162
def C6163 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 1, 0, 0, -2, 0]
theorem certificate6163 : C6163.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6163 : ¬ (C6163.det = 0 ∧ ∀ i, C6163.adjugate i i ≠ 0) := by
  intro h
  have := certificate6163
  rw [h.1] at this
  norm_num at this
def C6164 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6164 : C6164.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6164 : ¬ (C6164.det = 0 ∧ ∀ i, C6164.adjugate i i ≠ 0) := by
  intro h
  have := certificate6164
  rw [h.1] at this
  norm_num at this
def C6165 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6165 : C6165.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6165 : ¬ (C6165.det = 0 ∧ ∀ i, C6165.adjugate i i ≠ 0) := by
  intro h
  have := certificate6165
  rw [h.1] at this
  norm_num at this
def C6166 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6166 : C6166.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6166 : ¬ (C6166.det = 0 ∧ ∀ i, C6166.adjugate i i ≠ 0) := by
  intro h
  have := certificate6166
  rw [h.1] at this
  norm_num at this
def C6167 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6167 : C6167.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6167 : ¬ (C6167.det = 0 ∧ ∀ i, C6167.adjugate i i ≠ 0) := by
  intro h
  have := certificate6167
  rw [h.1] at this
  norm_num at this
def C6168 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6168 : C6168.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6168 : ¬ (C6168.det = 0 ∧ ∀ i, C6168.adjugate i i ≠ 0) := by
  intro h
  have := certificate6168
  rw [h.1] at this
  norm_num at this
def C6169 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6169 : C6169.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6169 : ¬ (C6169.det = 0 ∧ ∀ i, C6169.adjugate i i ≠ 0) := by
  intro h
  have := certificate6169
  rw [h.1] at this
  norm_num at this
def C6170 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6170 : C6170.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6170 : ¬ (C6170.det = 0 ∧ ∀ i, C6170.adjugate i i ≠ 0) := by
  intro h
  have := certificate6170
  rw [h.1] at this
  norm_num at this
def C6171 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6171 : C6171.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6171 : ¬ (C6171.det = 0 ∧ ∀ i, C6171.adjugate i i ≠ 0) := by
  intro h
  have := certificate6171
  rw [h.1] at this
  norm_num at this
def C6172 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6172 : C6172.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6172 : ¬ (C6172.det = 0 ∧ ∀ i, C6172.adjugate i i ≠ 0) := by
  intro h
  have := certificate6172
  rw [h.1] at this
  norm_num at this
def C6173 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6173 : C6173.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6173 : ¬ (C6173.det = 0 ∧ ∀ i, C6173.adjugate i i ≠ 0) := by
  intro h
  have := certificate6173
  rw [h.1] at this
  norm_num at this
def C6174 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6174 : C6174.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6174 : ¬ (C6174.det = 0 ∧ ∀ i, C6174.adjugate i i ≠ 0) := by
  intro h
  have := certificate6174
  rw [h.1] at this
  norm_num at this
def C6175 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6175 : C6175.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6175 : ¬ (C6175.det = 0 ∧ ∀ i, C6175.adjugate i i ≠ 0) := by
  intro h
  have := certificate6175
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0192
