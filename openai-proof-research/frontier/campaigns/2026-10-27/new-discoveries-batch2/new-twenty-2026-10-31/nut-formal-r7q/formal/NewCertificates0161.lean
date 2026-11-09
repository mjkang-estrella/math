import VerifiedDet
namespace Nut8.NewCertificates0161
def C5152 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5152 : C5152.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5152 : ¬ (C5152.det = 0 ∧ ∀ i, C5152.adjugate i i ≠ 0) := by
  intro h
  have := certificate5152
  rw [h.1] at this
  norm_num at this
def C5153 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5153 : C5153.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5153 : ¬ (C5153.det = 0 ∧ ∀ i, C5153.adjugate i i ≠ 0) := by
  intro h
  have := certificate5153
  rw [h.1] at this
  norm_num at this
def C5154 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5154 : C5154.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5154 : ¬ (C5154.det = 0 ∧ ∀ i, C5154.adjugate i i ≠ 0) := by
  intro h
  have := certificate5154
  rw [h.1] at this
  norm_num at this
def C5155 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5155 : C5155.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5155 : ¬ (C5155.det = 0 ∧ ∀ i, C5155.adjugate i i ≠ 0) := by
  intro h
  have := certificate5155
  rw [h.1] at this
  norm_num at this
def C5156 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5156 : C5156.det = (41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5156 : ¬ (C5156.det = 0 ∧ ∀ i, C5156.adjugate i i ≠ 0) := by
  intro h
  have := certificate5156
  rw [h.1] at this
  norm_num at this
def C5157 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5157 : C5157.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5157 : ¬ (C5157.det = 0 ∧ ∀ i, C5157.adjugate i i ≠ 0) := by
  intro h
  have := certificate5157
  rw [h.1] at this
  norm_num at this
def C5158 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5158 : C5158.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5158 : ¬ (C5158.det = 0 ∧ ∀ i, C5158.adjugate i i ≠ 0) := by
  intro h
  have := certificate5158
  rw [h.1] at this
  norm_num at this
def C5159 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5159 : C5159.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5159 : ¬ (C5159.det = 0 ∧ ∀ i, C5159.adjugate i i ≠ 0) := by
  intro h
  have := certificate5159
  rw [h.1] at this
  norm_num at this
def C5160 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5160 : C5160.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5160 : ¬ (C5160.det = 0 ∧ ∀ i, C5160.adjugate i i ≠ 0) := by
  intro h
  have := certificate5160
  rw [h.1] at this
  norm_num at this
def C5161 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5161 : C5161.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5161 : ¬ (C5161.det = 0 ∧ ∀ i, C5161.adjugate i i ≠ 0) := by
  intro h
  have := certificate5161
  rw [h.1] at this
  norm_num at this
def C5162 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5162 : C5162.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5162 : ¬ (C5162.det = 0 ∧ ∀ i, C5162.adjugate i i ≠ 0) := by
  intro h
  have := certificate5162
  rw [h.1] at this
  norm_num at this
def C5163 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5163 : C5163.det = (-87 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5163 : ¬ (C5163.det = 0 ∧ ∀ i, C5163.adjugate i i ≠ 0) := by
  intro h
  have := certificate5163
  rw [h.1] at this
  norm_num at this
def C5164 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5164 : C5164.det = (-67 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5164 : ¬ (C5164.det = 0 ∧ ∀ i, C5164.adjugate i i ≠ 0) := by
  intro h
  have := certificate5164
  rw [h.1] at this
  norm_num at this
def C5165 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5165 : C5165.det = (61 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5165 : ¬ (C5165.det = 0 ∧ ∀ i, C5165.adjugate i i ≠ 0) := by
  intro h
  have := certificate5165
  rw [h.1] at this
  norm_num at this
def C5166 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5166 : C5166.det = (-67 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5166 : ¬ (C5166.det = 0 ∧ ∀ i, C5166.adjugate i i ≠ 0) := by
  intro h
  have := certificate5166
  rw [h.1] at this
  norm_num at this
def C5167 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5167 : C5167.det = (61 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5167 : ¬ (C5167.det = 0 ∧ ∀ i, C5167.adjugate i i ≠ 0) := by
  intro h
  have := certificate5167
  rw [h.1] at this
  norm_num at this
def C5168 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5168 : C5168.det = (105 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5168 : ¬ (C5168.det = 0 ∧ ∀ i, C5168.adjugate i i ≠ 0) := by
  intro h
  have := certificate5168
  rw [h.1] at this
  norm_num at this
def C5169 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5169 : C5169.det = (-31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5169 : ¬ (C5169.det = 0 ∧ ∀ i, C5169.adjugate i i ≠ 0) := by
  intro h
  have := certificate5169
  rw [h.1] at this
  norm_num at this
def C5170 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5170 : C5170.det = (-31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5170 : ¬ (C5170.det = 0 ∧ ∀ i, C5170.adjugate i i ≠ 0) := by
  intro h
  have := certificate5170
  rw [h.1] at this
  norm_num at this
def C5171 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5171 : C5171.det = (105 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5171 : ¬ (C5171.det = 0 ∧ ∀ i, C5171.adjugate i i ≠ 0) := by
  intro h
  have := certificate5171
  rw [h.1] at this
  norm_num at this
def C5172 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5172 : C5172.det = (61 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5172 : ¬ (C5172.det = 0 ∧ ∀ i, C5172.adjugate i i ≠ 0) := by
  intro h
  have := certificate5172
  rw [h.1] at this
  norm_num at this
def C5173 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5173 : C5173.det = (-67 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5173 : ¬ (C5173.det = 0 ∧ ∀ i, C5173.adjugate i i ≠ 0) := by
  intro h
  have := certificate5173
  rw [h.1] at this
  norm_num at this
def C5174 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5174 : C5174.det = (61 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5174 : ¬ (C5174.det = 0 ∧ ∀ i, C5174.adjugate i i ≠ 0) := by
  intro h
  have := certificate5174
  rw [h.1] at this
  norm_num at this
def C5175 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5175 : C5175.det = (-67 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5175 : ¬ (C5175.det = 0 ∧ ∀ i, C5175.adjugate i i ≠ 0) := by
  intro h
  have := certificate5175
  rw [h.1] at this
  norm_num at this
def C5176 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5176 : C5176.det = (-87 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5176 : ¬ (C5176.det = 0 ∧ ∀ i, C5176.adjugate i i ≠ 0) := by
  intro h
  have := certificate5176
  rw [h.1] at this
  norm_num at this
def C5177 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5177 : C5177.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5177 : ¬ (C5177.det = 0 ∧ ∀ i, C5177.adjugate i i ≠ 0) := by
  intro h
  have := certificate5177
  rw [h.1] at this
  norm_num at this
def C5178 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5178 : C5178.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5178 : ¬ (C5178.det = 0 ∧ ∀ i, C5178.adjugate i i ≠ 0) := by
  intro h
  have := certificate5178
  rw [h.1] at this
  norm_num at this
def C5179 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5179 : C5179.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5179 : ¬ (C5179.det = 0 ∧ ∀ i, C5179.adjugate i i ≠ 0) := by
  intro h
  have := certificate5179
  rw [h.1] at this
  norm_num at this
def C5180 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5180 : C5180.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5180 : ¬ (C5180.det = 0 ∧ ∀ i, C5180.adjugate i i ≠ 0) := by
  intro h
  have := certificate5180
  rw [h.1] at this
  norm_num at this
def C5181 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5181 : C5181.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5181 : ¬ (C5181.det = 0 ∧ ∀ i, C5181.adjugate i i ≠ 0) := by
  intro h
  have := certificate5181
  rw [h.1] at this
  norm_num at this
def C5182 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5182 : C5182.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5182 : ¬ (C5182.det = 0 ∧ ∀ i, C5182.adjugate i i ≠ 0) := by
  intro h
  have := certificate5182
  rw [h.1] at this
  norm_num at this
def C5183 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5183 : C5183.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5183 : ¬ (C5183.det = 0 ∧ ∀ i, C5183.adjugate i i ≠ 0) := by
  intro h
  have := certificate5183
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0161
