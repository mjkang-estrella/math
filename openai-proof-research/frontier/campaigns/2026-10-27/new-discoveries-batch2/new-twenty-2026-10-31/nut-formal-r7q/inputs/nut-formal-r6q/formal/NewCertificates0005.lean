import VerifiedDet
namespace Nut8.NewCertificates0005
def C160 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate160 : C160.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction160 : ¬ (C160.det = 0 ∧ ∀ i, C160.adjugate i i ≠ 0) := by
  intro h
  have := certificate160
  rw [h.1] at this
  norm_num at this
def C161 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate161 : C161.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction161 : ¬ (C161.det = 0 ∧ ∀ i, C161.adjugate i i ≠ 0) := by
  intro h
  have := certificate161
  rw [h.1] at this
  norm_num at this
def C162 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate162 : C162.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction162 : ¬ (C162.det = 0 ∧ ∀ i, C162.adjugate i i ≠ 0) := by
  intro h
  have := certificate162
  rw [h.1] at this
  norm_num at this
def C163 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate163 : C163.det = (92 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction163 : ¬ (C163.det = 0 ∧ ∀ i, C163.adjugate i i ≠ 0) := by
  intro h
  have := certificate163
  rw [h.1] at this
  norm_num at this
def C164 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate164 : C164.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction164 : ¬ (C164.det = 0 ∧ ∀ i, C164.adjugate i i ≠ 0) := by
  intro h
  have := certificate164
  rw [h.1] at this
  norm_num at this
def C165 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate165 : C165.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction165 : ¬ (C165.det = 0 ∧ ∀ i, C165.adjugate i i ≠ 0) := by
  intro h
  have := certificate165
  rw [h.1] at this
  norm_num at this
def C166 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate166 : C166.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction166 : ¬ (C166.det = 0 ∧ ∀ i, C166.adjugate i i ≠ 0) := by
  intro h
  have := certificate166
  rw [h.1] at this
  norm_num at this
def C167 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate167 : C167.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction167 : ¬ (C167.det = 0 ∧ ∀ i, C167.adjugate i i ≠ 0) := by
  intro h
  have := certificate167
  rw [h.1] at this
  norm_num at this
def C168 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate168 : C168.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction168 : ¬ (C168.det = 0 ∧ ∀ i, C168.adjugate i i ≠ 0) := by
  intro h
  have := certificate168
  rw [h.1] at this
  norm_num at this
def C169 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate169 : C169.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction169 : ¬ (C169.det = 0 ∧ ∀ i, C169.adjugate i i ≠ 0) := by
  intro h
  have := certificate169
  rw [h.1] at this
  norm_num at this
def C170 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate170 : C170.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction170 : ¬ (C170.det = 0 ∧ ∀ i, C170.adjugate i i ≠ 0) := by
  intro h
  have := certificate170
  rw [h.1] at this
  norm_num at this
def C171 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate171 : C171.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction171 : ¬ (C171.det = 0 ∧ ∀ i, C171.adjugate i i ≠ 0) := by
  intro h
  have := certificate171
  rw [h.1] at this
  norm_num at this
def C172 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate172 : C172.det = (92 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction172 : ¬ (C172.det = 0 ∧ ∀ i, C172.adjugate i i ≠ 0) := by
  intro h
  have := certificate172
  rw [h.1] at this
  norm_num at this
def C173 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate173 : C173.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction173 : ¬ (C173.det = 0 ∧ ∀ i, C173.adjugate i i ≠ 0) := by
  intro h
  have := certificate173
  rw [h.1] at this
  norm_num at this
def C174 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate174 : C174.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction174 : ¬ (C174.det = 0 ∧ ∀ i, C174.adjugate i i ≠ 0) := by
  intro h
  have := certificate174
  rw [h.1] at this
  norm_num at this
def C175 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate175 : C175.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction175 : ¬ (C175.det = 0 ∧ ∀ i, C175.adjugate i i ≠ 0) := by
  intro h
  have := certificate175
  rw [h.1] at this
  norm_num at this
def C176 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate176 : C176.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction176 : ¬ (C176.det = 0 ∧ ∀ i, C176.adjugate i i ≠ 0) := by
  intro h
  have := certificate176
  rw [h.1] at this
  norm_num at this
def C177 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate177 : C177.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction177 : ¬ (C177.det = 0 ∧ ∀ i, C177.adjugate i i ≠ 0) := by
  intro h
  have := certificate177
  rw [h.1] at this
  norm_num at this
def C178 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate178 : C178.det = (-88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction178 : ¬ (C178.det = 0 ∧ ∀ i, C178.adjugate i i ≠ 0) := by
  intro h
  have := certificate178
  rw [h.1] at this
  norm_num at this
def C179 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate179 : C179.det = (104 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction179 : ¬ (C179.det = 0 ∧ ∀ i, C179.adjugate i i ≠ 0) := by
  intro h
  have := certificate179
  rw [h.1] at this
  norm_num at this
def C180 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate180 : C180.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction180 : ¬ (C180.det = 0 ∧ ∀ i, C180.adjugate i i ≠ 0) := by
  intro h
  have := certificate180
  rw [h.1] at this
  norm_num at this
def C181 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate181 : C181.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction181 : ¬ (C181.det = 0 ∧ ∀ i, C181.adjugate i i ≠ 0) := by
  intro h
  have := certificate181
  rw [h.1] at this
  norm_num at this
def C182 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate182 : C182.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction182 : ¬ (C182.det = 0 ∧ ∀ i, C182.adjugate i i ≠ 0) := by
  intro h
  have := certificate182
  rw [h.1] at this
  norm_num at this
def C183 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate183 : C183.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction183 : ¬ (C183.det = 0 ∧ ∀ i, C183.adjugate i i ≠ 0) := by
  intro h
  have := certificate183
  rw [h.1] at this
  norm_num at this
def C184 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate184 : C184.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction184 : ¬ (C184.det = 0 ∧ ∀ i, C184.adjugate i i ≠ 0) := by
  intro h
  have := certificate184
  rw [h.1] at this
  norm_num at this
def C185 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate185 : C185.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction185 : ¬ (C185.det = 0 ∧ ∀ i, C185.adjugate i i ≠ 0) := by
  intro h
  have := certificate185
  rw [h.1] at this
  norm_num at this
def C186 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate186 : C186.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction186 : ¬ (C186.det = 0 ∧ ∀ i, C186.adjugate i i ≠ 0) := by
  intro h
  have := certificate186
  rw [h.1] at this
  norm_num at this
def C187 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate187 : C187.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction187 : ¬ (C187.det = 0 ∧ ∀ i, C187.adjugate i i ≠ 0) := by
  intro h
  have := certificate187
  rw [h.1] at this
  norm_num at this
def C188 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate188 : C188.det = (104 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction188 : ¬ (C188.det = 0 ∧ ∀ i, C188.adjugate i i ≠ 0) := by
  intro h
  have := certificate188
  rw [h.1] at this
  norm_num at this
def C189 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate189 : C189.det = (-88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction189 : ¬ (C189.det = 0 ∧ ∀ i, C189.adjugate i i ≠ 0) := by
  intro h
  have := certificate189
  rw [h.1] at this
  norm_num at this
def C190 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate190 : C190.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction190 : ¬ (C190.det = 0 ∧ ∀ i, C190.adjugate i i ≠ 0) := by
  intro h
  have := certificate190
  rw [h.1] at this
  norm_num at this
def C191 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate191 : C191.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction191 : ¬ (C191.det = 0 ∧ ∀ i, C191.adjugate i i ≠ 0) := by
  intro h
  have := certificate191
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0005
