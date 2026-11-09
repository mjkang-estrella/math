import VerifiedDet
namespace Nut8.NewCertificates0193
def C6176 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6176 : C6176.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6176 : ¬ (C6176.det = 0 ∧ ∀ i, C6176.adjugate i i ≠ 0) := by
  intro h
  have := certificate6176
  rw [h.1] at this
  norm_num at this
def C6177 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6177 : C6177.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6177 : ¬ (C6177.det = 0 ∧ ∀ i, C6177.adjugate i i ≠ 0) := by
  intro h
  have := certificate6177
  rw [h.1] at this
  norm_num at this
def C6178 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6178 : C6178.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6178 : ¬ (C6178.det = 0 ∧ ∀ i, C6178.adjugate i i ≠ 0) := by
  intro h
  have := certificate6178
  rw [h.1] at this
  norm_num at this
def C6179 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6179 : C6179.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6179 : ¬ (C6179.det = 0 ∧ ∀ i, C6179.adjugate i i ≠ 0) := by
  intro h
  have := certificate6179
  rw [h.1] at this
  norm_num at this
def C6180 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6180 : C6180.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6180 : ¬ (C6180.det = 0 ∧ ∀ i, C6180.adjugate i i ≠ 0) := by
  intro h
  have := certificate6180
  rw [h.1] at this
  norm_num at this
def C6181 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6181 : C6181.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6181 : ¬ (C6181.det = 0 ∧ ∀ i, C6181.adjugate i i ≠ 0) := by
  intro h
  have := certificate6181
  rw [h.1] at this
  norm_num at this
def C6182 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6182 : C6182.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6182 : ¬ (C6182.det = 0 ∧ ∀ i, C6182.adjugate i i ≠ 0) := by
  intro h
  have := certificate6182
  rw [h.1] at this
  norm_num at this
def C6183 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6183 : C6183.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6183 : ¬ (C6183.det = 0 ∧ ∀ i, C6183.adjugate i i ≠ 0) := by
  intro h
  have := certificate6183
  rw [h.1] at this
  norm_num at this
def C6184 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6184 : C6184.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6184 : ¬ (C6184.det = 0 ∧ ∀ i, C6184.adjugate i i ≠ 0) := by
  intro h
  have := certificate6184
  rw [h.1] at this
  norm_num at this
def C6185 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6185 : C6185.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6185 : ¬ (C6185.det = 0 ∧ ∀ i, C6185.adjugate i i ≠ 0) := by
  intro h
  have := certificate6185
  rw [h.1] at this
  norm_num at this
def C6186 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6186 : C6186.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6186 : ¬ (C6186.det = 0 ∧ ∀ i, C6186.adjugate i i ≠ 0) := by
  intro h
  have := certificate6186
  rw [h.1] at this
  norm_num at this
def C6187 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6187 : C6187.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6187 : ¬ (C6187.det = 0 ∧ ∀ i, C6187.adjugate i i ≠ 0) := by
  intro h
  have := certificate6187
  rw [h.1] at this
  norm_num at this
def C6188 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6188 : C6188.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6188 : ¬ (C6188.det = 0 ∧ ∀ i, C6188.adjugate i i ≠ 0) := by
  intro h
  have := certificate6188
  rw [h.1] at this
  norm_num at this
def C6189 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6189 : C6189.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6189 : ¬ (C6189.det = 0 ∧ ∀ i, C6189.adjugate i i ≠ 0) := by
  intro h
  have := certificate6189
  rw [h.1] at this
  norm_num at this
def C6190 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6190 : C6190.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6190 : ¬ (C6190.det = 0 ∧ ∀ i, C6190.adjugate i i ≠ 0) := by
  intro h
  have := certificate6190
  rw [h.1] at this
  norm_num at this
def C6191 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6191 : C6191.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6191 : ¬ (C6191.det = 0 ∧ ∀ i, C6191.adjugate i i ≠ 0) := by
  intro h
  have := certificate6191
  rw [h.1] at this
  norm_num at this
def C6192 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6192 : C6192.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6192 : ¬ (C6192.det = 0 ∧ ∀ i, C6192.adjugate i i ≠ 0) := by
  intro h
  have := certificate6192
  rw [h.1] at this
  norm_num at this
def C6193 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6193 : C6193.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6193 : ¬ (C6193.det = 0 ∧ ∀ i, C6193.adjugate i i ≠ 0) := by
  intro h
  have := certificate6193
  rw [h.1] at this
  norm_num at this
def C6194 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6194 : C6194.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6194 : ¬ (C6194.det = 0 ∧ ∀ i, C6194.adjugate i i ≠ 0) := by
  intro h
  have := certificate6194
  rw [h.1] at this
  norm_num at this
def C6195 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, -1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6195 : C6195.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6195 : ¬ (C6195.det = 0 ∧ ∀ i, C6195.adjugate i i ≠ 0) := by
  intro h
  have := certificate6195
  rw [h.1] at this
  norm_num at this
def C6196 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate6196 : C6196.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6196 : ¬ (C6196.det = 0 ∧ ∀ i, C6196.adjugate i i ≠ 0) := by
  intro h
  have := certificate6196
  rw [h.1] at this
  norm_num at this
def C6197 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate6197 : C6197.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6197 : ¬ (C6197.det = 0 ∧ ∀ i, C6197.adjugate i i ≠ 0) := by
  intro h
  have := certificate6197
  rw [h.1] at this
  norm_num at this
def C6198 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate6198 : C6198.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6198 : ¬ (C6198.det = 0 ∧ ∀ i, C6198.adjugate i i ≠ 0) := by
  intro h
  have := certificate6198
  rw [h.1] at this
  norm_num at this
def C6199 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate6199 : C6199.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6199 : ¬ (C6199.det = 0 ∧ ∀ i, C6199.adjugate i i ≠ 0) := by
  intro h
  have := certificate6199
  rw [h.1] at this
  norm_num at this
def C6200 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate6200 : C6200.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6200 : ¬ (C6200.det = 0 ∧ ∀ i, C6200.adjugate i i ≠ 0) := by
  intro h
  have := certificate6200
  rw [h.1] at this
  norm_num at this
def C6201 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate6201 : C6201.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6201 : ¬ (C6201.det = 0 ∧ ∀ i, C6201.adjugate i i ≠ 0) := by
  intro h
  have := certificate6201
  rw [h.1] at this
  norm_num at this
def C6202 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate6202 : C6202.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6202 : ¬ (C6202.det = 0 ∧ ∀ i, C6202.adjugate i i ≠ 0) := by
  intro h
  have := certificate6202
  rw [h.1] at this
  norm_num at this
def C6203 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate6203 : C6203.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6203 : ¬ (C6203.det = 0 ∧ ∀ i, C6203.adjugate i i ≠ 0) := by
  intro h
  have := certificate6203
  rw [h.1] at this
  norm_num at this
def C6204 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate6204 : C6204.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6204 : ¬ (C6204.det = 0 ∧ ∀ i, C6204.adjugate i i ≠ 0) := by
  intro h
  have := certificate6204
  rw [h.1] at this
  norm_num at this
def C6205 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate6205 : C6205.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6205 : ¬ (C6205.det = 0 ∧ ∀ i, C6205.adjugate i i ≠ 0) := by
  intro h
  have := certificate6205
  rw [h.1] at this
  norm_num at this
def C6206 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate6206 : C6206.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6206 : ¬ (C6206.det = 0 ∧ ∀ i, C6206.adjugate i i ≠ 0) := by
  intro h
  have := certificate6206
  rw [h.1] at this
  norm_num at this
def C6207 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate6207 : C6207.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6207 : ¬ (C6207.det = 0 ∧ ∀ i, C6207.adjugate i i ≠ 0) := by
  intro h
  have := certificate6207
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0193
