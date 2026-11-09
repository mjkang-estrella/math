import VerifiedDet
namespace Nut8.NewCertificates0254
def C8128 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8128 : C8128.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8128 : ¬ (C8128.det = 0 ∧ ∀ i, C8128.adjugate i i ≠ 0) := by
  intro h
  have := certificate8128
  rw [h.1] at this
  norm_num at this
def C8129 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8129 : C8129.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8129 : ¬ (C8129.det = 0 ∧ ∀ i, C8129.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8129
def C8130 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8130 : C8130.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8130 : ¬ (C8130.det = 0 ∧ ∀ i, C8130.adjugate i i ≠ 0) := by
  intro h
  have := certificate8130
  rw [h.1] at this
  norm_num at this
def C8131 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8131 : C8131.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8131 : ¬ (C8131.det = 0 ∧ ∀ i, C8131.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8131
def C8132 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8132 : C8132.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8132 : ¬ (C8132.det = 0 ∧ ∀ i, C8132.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8132
def C8133 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8133 : C8133.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8133 : ¬ (C8133.det = 0 ∧ ∀ i, C8133.adjugate i i ≠ 0) := by
  intro h
  have := certificate8133
  rw [h.1] at this
  norm_num at this
def C8134 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8134 : C8134.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8134 : ¬ (C8134.det = 0 ∧ ∀ i, C8134.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8134
def C8135 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8135 : C8135.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8135 : ¬ (C8135.det = 0 ∧ ∀ i, C8135.adjugate i i ≠ 0) := by
  intro h
  have := certificate8135
  rw [h.1] at this
  norm_num at this
def C8136 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8136 : C8136.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8136 : ¬ (C8136.det = 0 ∧ ∀ i, C8136.adjugate i i ≠ 0) := by
  intro h
  have := certificate8136
  rw [h.1] at this
  norm_num at this
def C8137 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8137 : C8137.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8137 : ¬ (C8137.det = 0 ∧ ∀ i, C8137.adjugate i i ≠ 0) := by
  intro h
  have := certificate8137
  rw [h.1] at this
  norm_num at this
def C8138 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8138 : C8138.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8138 : ¬ (C8138.det = 0 ∧ ∀ i, C8138.adjugate i i ≠ 0) := by
  intro h
  have := certificate8138
  rw [h.1] at this
  norm_num at this
def C8139 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8139 : C8139.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8139 : ¬ (C8139.det = 0 ∧ ∀ i, C8139.adjugate i i ≠ 0) := by
  intro h
  have := certificate8139
  rw [h.1] at this
  norm_num at this
def C8140 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8140 : C8140.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8140 : ¬ (C8140.det = 0 ∧ ∀ i, C8140.adjugate i i ≠ 0) := by
  intro h
  have := certificate8140
  rw [h.1] at this
  norm_num at this
def C8141 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8141 : C8141.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8141 : ¬ (C8141.det = 0 ∧ ∀ i, C8141.adjugate i i ≠ 0) := by
  intro h
  have := certificate8141
  rw [h.1] at this
  norm_num at this
def C8142 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8142 : C8142.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8142 : ¬ (C8142.det = 0 ∧ ∀ i, C8142.adjugate i i ≠ 0) := by
  intro h
  have := certificate8142
  rw [h.1] at this
  norm_num at this
def C8143 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8143 : C8143.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8143 : ¬ (C8143.det = 0 ∧ ∀ i, C8143.adjugate i i ≠ 0) := by
  intro h
  have := certificate8143
  rw [h.1] at this
  norm_num at this
def C8144 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8144 : C8144.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8144 : ¬ (C8144.det = 0 ∧ ∀ i, C8144.adjugate i i ≠ 0) := by
  intro h
  have := certificate8144
  rw [h.1] at this
  norm_num at this
def C8145 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8145 : C8145.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8145 : ¬ (C8145.det = 0 ∧ ∀ i, C8145.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8145
def C8146 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8146 : C8146.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8146 : ¬ (C8146.det = 0 ∧ ∀ i, C8146.adjugate i i ≠ 0) := by
  intro h
  have := certificate8146
  rw [h.1] at this
  norm_num at this
def C8147 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8147 : C8147.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8147 : ¬ (C8147.det = 0 ∧ ∀ i, C8147.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8147
def C8148 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8148 : C8148.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8148 : ¬ (C8148.det = 0 ∧ ∀ i, C8148.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8148
def C8149 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8149 : C8149.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8149 : ¬ (C8149.det = 0 ∧ ∀ i, C8149.adjugate i i ≠ 0) := by
  intro h
  have := certificate8149
  rw [h.1] at this
  norm_num at this
def C8150 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8150 : C8150.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8150 : ¬ (C8150.det = 0 ∧ ∀ i, C8150.adjugate i i ≠ 0) := by
  intro h
  have := certificate8150
  rw [h.1] at this
  norm_num at this
def C8151 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8151 : C8151.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8151 : ¬ (C8151.det = 0 ∧ ∀ i, C8151.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8151
def C8152 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8152 : C8152.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8152 : ¬ (C8152.det = 0 ∧ ∀ i, C8152.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8152
def C8153 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8153 : C8153.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8153 : ¬ (C8153.det = 0 ∧ ∀ i, C8153.adjugate i i ≠ 0) := by
  intro h
  have := certificate8153
  rw [h.1] at this
  norm_num at this
def C8154 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8154 : C8154.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8154 : ¬ (C8154.det = 0 ∧ ∀ i, C8154.adjugate i i ≠ 0) := by
  intro h
  have := certificate8154
  rw [h.1] at this
  norm_num at this
def C8155 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8155 : C8155.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8155 : ¬ (C8155.det = 0 ∧ ∀ i, C8155.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8155
def C8156 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8156 : C8156.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8156 : ¬ (C8156.det = 0 ∧ ∀ i, C8156.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8156
def C8157 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8157 : C8157.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8157 : ¬ (C8157.det = 0 ∧ ∀ i, C8157.adjugate i i ≠ 0) := by
  intro h
  have := certificate8157
  rw [h.1] at this
  norm_num at this
def C8158 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8158 : C8158.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8158 : ¬ (C8158.det = 0 ∧ ∀ i, C8158.adjugate i i ≠ 0) := by
  intro h
  have := certificate8158
  rw [h.1] at this
  norm_num at this
def C8159 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8159 : C8159.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8159 : ¬ (C8159.det = 0 ∧ ∀ i, C8159.adjugate i i ≠ 0) := by
  intro h
  have := certificate8159
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0254
