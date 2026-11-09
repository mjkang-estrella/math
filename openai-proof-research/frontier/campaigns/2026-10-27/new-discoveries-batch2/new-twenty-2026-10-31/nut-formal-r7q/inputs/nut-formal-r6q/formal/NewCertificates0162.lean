import VerifiedDet
namespace Nut8.NewCertificates0162
def C5184 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5184 : C5184.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5184 : ¬ (C5184.det = 0 ∧ ∀ i, C5184.adjugate i i ≠ 0) := by
  intro h
  have := certificate5184
  rw [h.1] at this
  norm_num at this
def C5185 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5185 : C5185.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5185 : ¬ (C5185.det = 0 ∧ ∀ i, C5185.adjugate i i ≠ 0) := by
  intro h
  have := certificate5185
  rw [h.1] at this
  norm_num at this
def C5186 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5186 : C5186.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5186 : ¬ (C5186.det = 0 ∧ ∀ i, C5186.adjugate i i ≠ 0) := by
  intro h
  have := certificate5186
  rw [h.1] at this
  norm_num at this
def C5187 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5187 : C5187.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5187 : ¬ (C5187.det = 0 ∧ ∀ i, C5187.adjugate i i ≠ 0) := by
  intro h
  have := certificate5187
  rw [h.1] at this
  norm_num at this
def C5188 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5188 : C5188.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5188 : ¬ (C5188.det = 0 ∧ ∀ i, C5188.adjugate i i ≠ 0) := by
  intro h
  have := certificate5188
  rw [h.1] at this
  norm_num at this
def C5189 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5189 : C5189.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5189 : ¬ (C5189.det = 0 ∧ ∀ i, C5189.adjugate i i ≠ 0) := by
  intro h
  have := certificate5189
  rw [h.1] at this
  norm_num at this
def C5190 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5190 : C5190.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5190 : ¬ (C5190.det = 0 ∧ ∀ i, C5190.adjugate i i ≠ 0) := by
  intro h
  have := certificate5190
  rw [h.1] at this
  norm_num at this
def C5191 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5191 : C5191.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5191 : ¬ (C5191.det = 0 ∧ ∀ i, C5191.adjugate i i ≠ 0) := by
  intro h
  have := certificate5191
  rw [h.1] at this
  norm_num at this
def C5192 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5192 : C5192.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5192 : ¬ (C5192.det = 0 ∧ ∀ i, C5192.adjugate i i ≠ 0) := by
  intro h
  have := certificate5192
  rw [h.1] at this
  norm_num at this
def C5193 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5193 : C5193.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5193 : ¬ (C5193.det = 0 ∧ ∀ i, C5193.adjugate i i ≠ 0) := by
  intro h
  have := certificate5193
  rw [h.1] at this
  norm_num at this
def C5194 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5194 : C5194.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5194 : ¬ (C5194.det = 0 ∧ ∀ i, C5194.adjugate i i ≠ 0) := by
  intro h
  have := certificate5194
  rw [h.1] at this
  norm_num at this
def C5195 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5195 : C5195.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5195 : ¬ (C5195.det = 0 ∧ ∀ i, C5195.adjugate i i ≠ 0) := by
  intro h
  have := certificate5195
  rw [h.1] at this
  norm_num at this
def C5196 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5196 : C5196.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5196 : ¬ (C5196.det = 0 ∧ ∀ i, C5196.adjugate i i ≠ 0) := by
  intro h
  have := certificate5196
  rw [h.1] at this
  norm_num at this
def C5197 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5197 : C5197.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5197 : ¬ (C5197.det = 0 ∧ ∀ i, C5197.adjugate i i ≠ 0) := by
  intro h
  have := certificate5197
  rw [h.1] at this
  norm_num at this
def C5198 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5198 : C5198.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5198 : ¬ (C5198.det = 0 ∧ ∀ i, C5198.adjugate i i ≠ 0) := by
  intro h
  have := certificate5198
  rw [h.1] at this
  norm_num at this
def C5199 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5199 : C5199.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5199 : ¬ (C5199.det = 0 ∧ ∀ i, C5199.adjugate i i ≠ 0) := by
  intro h
  have := certificate5199
  rw [h.1] at this
  norm_num at this
def C5200 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5200 : C5200.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5200 : ¬ (C5200.det = 0 ∧ ∀ i, C5200.adjugate i i ≠ 0) := by
  intro h
  have := certificate5200
  rw [h.1] at this
  norm_num at this
def C5201 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5201 : C5201.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5201 : ¬ (C5201.det = 0 ∧ ∀ i, C5201.adjugate i i ≠ 0) := by
  intro h
  have := certificate5201
  rw [h.1] at this
  norm_num at this
def C5202 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5202 : C5202.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5202 : ¬ (C5202.det = 0 ∧ ∀ i, C5202.adjugate i i ≠ 0) := by
  intro h
  have := certificate5202
  rw [h.1] at this
  norm_num at this
def C5203 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5203 : C5203.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5203 : ¬ (C5203.det = 0 ∧ ∀ i, C5203.adjugate i i ≠ 0) := by
  intro h
  have := certificate5203
  rw [h.1] at this
  norm_num at this
def C5204 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5204 : C5204.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5204 : ¬ (C5204.det = 0 ∧ ∀ i, C5204.adjugate i i ≠ 0) := by
  intro h
  have := certificate5204
  rw [h.1] at this
  norm_num at this
def C5205 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5205 : C5205.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5205 : ¬ (C5205.det = 0 ∧ ∀ i, C5205.adjugate i i ≠ 0) := by
  intro h
  have := certificate5205
  rw [h.1] at this
  norm_num at this
def C5206 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5206 : C5206.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5206 : ¬ (C5206.det = 0 ∧ ∀ i, C5206.adjugate i i ≠ 0) := by
  intro h
  have := certificate5206
  rw [h.1] at this
  norm_num at this
def C5207 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5207 : C5207.det = (73 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5207 : ¬ (C5207.det = 0 ∧ ∀ i, C5207.adjugate i i ≠ 0) := by
  intro h
  have := certificate5207
  rw [h.1] at this
  norm_num at this
def C5208 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5208 : C5208.det = (73 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5208 : ¬ (C5208.det = 0 ∧ ∀ i, C5208.adjugate i i ≠ 0) := by
  intro h
  have := certificate5208
  rw [h.1] at this
  norm_num at this
def C5209 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5209 : C5209.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5209 : ¬ (C5209.det = 0 ∧ ∀ i, C5209.adjugate i i ≠ 0) := by
  intro h
  have := certificate5209
  rw [h.1] at this
  norm_num at this
def C5210 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5210 : C5210.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5210 : ¬ (C5210.det = 0 ∧ ∀ i, C5210.adjugate i i ≠ 0) := by
  intro h
  have := certificate5210
  rw [h.1] at this
  norm_num at this
def C5211 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate5211 : C5211.det = (73 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5211 : ¬ (C5211.det = 0 ∧ ∀ i, C5211.adjugate i i ≠ 0) := by
  intro h
  have := certificate5211
  rw [h.1] at this
  norm_num at this
def C5212 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5212 : C5212.det = (73 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5212 : ¬ (C5212.det = 0 ∧ ∀ i, C5212.adjugate i i ≠ 0) := by
  intro h
  have := certificate5212
  rw [h.1] at this
  norm_num at this
def C5213 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate5213 : C5213.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5213 : ¬ (C5213.det = 0 ∧ ∀ i, C5213.adjugate i i ≠ 0) := by
  intro h
  have := certificate5213
  rw [h.1] at this
  norm_num at this
def C5214 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate5214 : C5214.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5214 : ¬ (C5214.det = 0 ∧ ∀ i, C5214.adjugate i i ≠ 0) := by
  intro h
  have := certificate5214
  rw [h.1] at this
  norm_num at this
def C5215 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate5215 : C5215.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5215 : ¬ (C5215.det = 0 ∧ ∀ i, C5215.adjugate i i ≠ 0) := by
  intro h
  have := certificate5215
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0162
