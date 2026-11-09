import VerifiedDet
namespace Nut8.NewCertificates0098
def C3136 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3136 : C3136.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3136 : ¬ (C3136.det = 0 ∧ ∀ i, C3136.adjugate i i ≠ 0) := by
  intro h
  have := certificate3136
  rw [h.1] at this
  norm_num at this
def C3137 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3137 : C3137.det = (-41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3137 : ¬ (C3137.det = 0 ∧ ∀ i, C3137.adjugate i i ≠ 0) := by
  intro h
  have := certificate3137
  rw [h.1] at this
  norm_num at this
def C3138 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3138 : C3138.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3138 : ¬ (C3138.det = 0 ∧ ∀ i, C3138.adjugate i i ≠ 0) := by
  intro h
  have := certificate3138
  rw [h.1] at this
  norm_num at this
def C3139 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3139 : C3139.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3139 : ¬ (C3139.det = 0 ∧ ∀ i, C3139.adjugate i i ≠ 0) := by
  intro h
  have := certificate3139
  rw [h.1] at this
  norm_num at this
def C3140 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3140 : C3140.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3140 : ¬ (C3140.det = 0 ∧ ∀ i, C3140.adjugate i i ≠ 0) := by
  intro h
  have := certificate3140
  rw [h.1] at this
  norm_num at this
def C3141 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3141 : C3141.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3141 : ¬ (C3141.det = 0 ∧ ∀ i, C3141.adjugate i i ≠ 0) := by
  intro h
  have := certificate3141
  rw [h.1] at this
  norm_num at this
def C3142 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3142 : C3142.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3142 : ¬ (C3142.det = 0 ∧ ∀ i, C3142.adjugate i i ≠ 0) := by
  intro h
  have := certificate3142
  rw [h.1] at this
  norm_num at this
def C3143 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3143 : C3143.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3143 : ¬ (C3143.det = 0 ∧ ∀ i, C3143.adjugate i i ≠ 0) := by
  intro h
  have := certificate3143
  rw [h.1] at this
  norm_num at this
def C3144 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3144 : C3144.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3144 : ¬ (C3144.det = 0 ∧ ∀ i, C3144.adjugate i i ≠ 0) := by
  intro h
  have := certificate3144
  rw [h.1] at this
  norm_num at this
def C3145 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3145 : C3145.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3145 : ¬ (C3145.det = 0 ∧ ∀ i, C3145.adjugate i i ≠ 0) := by
  intro h
  have := certificate3145
  rw [h.1] at this
  norm_num at this
def C3146 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3146 : C3146.det = (-41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3146 : ¬ (C3146.det = 0 ∧ ∀ i, C3146.adjugate i i ≠ 0) := by
  intro h
  have := certificate3146
  rw [h.1] at this
  norm_num at this
def C3147 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3147 : C3147.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3147 : ¬ (C3147.det = 0 ∧ ∀ i, C3147.adjugate i i ≠ 0) := by
  intro h
  have := certificate3147
  rw [h.1] at this
  norm_num at this
def C3148 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3148 : C3148.det = (55 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3148 : ¬ (C3148.det = 0 ∧ ∀ i, C3148.adjugate i i ≠ 0) := by
  intro h
  have := certificate3148
  rw [h.1] at this
  norm_num at this
def C3149 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3149 : C3149.det = (-45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3149 : ¬ (C3149.det = 0 ∧ ∀ i, C3149.adjugate i i ≠ 0) := by
  intro h
  have := certificate3149
  rw [h.1] at this
  norm_num at this
def C3150 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3150 : C3150.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3150 : ¬ (C3150.det = 0 ∧ ∀ i, C3150.adjugate i i ≠ 0) := by
  intro h
  have := certificate3150
  rw [h.1] at this
  norm_num at this
def C3151 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3151 : C3151.det = (82 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3151 : ¬ (C3151.det = 0 ∧ ∀ i, C3151.adjugate i i ≠ 0) := by
  intro h
  have := certificate3151
  rw [h.1] at this
  norm_num at this
def C3152 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3152 : C3152.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3152 : ¬ (C3152.det = 0 ∧ ∀ i, C3152.adjugate i i ≠ 0) := by
  intro h
  have := certificate3152
  rw [h.1] at this
  norm_num at this
def C3153 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3153 : C3153.det = (-26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3153 : ¬ (C3153.det = 0 ∧ ∀ i, C3153.adjugate i i ≠ 0) := by
  intro h
  have := certificate3153
  rw [h.1] at this
  norm_num at this
def C3154 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3154 : C3154.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3154 : ¬ (C3154.det = 0 ∧ ∀ i, C3154.adjugate i i ≠ 0) := by
  intro h
  have := certificate3154
  rw [h.1] at this
  norm_num at this
def C3155 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3155 : C3155.det = (-54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3155 : ¬ (C3155.det = 0 ∧ ∀ i, C3155.adjugate i i ≠ 0) := by
  intro h
  have := certificate3155
  rw [h.1] at this
  norm_num at this
def C3156 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3156 : C3156.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3156 : ¬ (C3156.det = 0 ∧ ∀ i, C3156.adjugate i i ≠ 0) := by
  intro h
  have := certificate3156
  rw [h.1] at this
  norm_num at this
def C3157 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3157 : C3157.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3157 : ¬ (C3157.det = 0 ∧ ∀ i, C3157.adjugate i i ≠ 0) := by
  intro h
  have := certificate3157
  rw [h.1] at this
  norm_num at this
def C3158 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3158 : C3158.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3158 : ¬ (C3158.det = 0 ∧ ∀ i, C3158.adjugate i i ≠ 0) := by
  intro h
  have := certificate3158
  rw [h.1] at this
  norm_num at this
def C3159 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3159 : C3159.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3159 : ¬ (C3159.det = 0 ∧ ∀ i, C3159.adjugate i i ≠ 0) := by
  intro h
  have := certificate3159
  rw [h.1] at this
  norm_num at this
def C3160 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3160 : C3160.det = (-54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3160 : ¬ (C3160.det = 0 ∧ ∀ i, C3160.adjugate i i ≠ 0) := by
  intro h
  have := certificate3160
  rw [h.1] at this
  norm_num at this
def C3161 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3161 : C3161.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3161 : ¬ (C3161.det = 0 ∧ ∀ i, C3161.adjugate i i ≠ 0) := by
  intro h
  have := certificate3161
  rw [h.1] at this
  norm_num at this
def C3162 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3162 : C3162.det = (-26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3162 : ¬ (C3162.det = 0 ∧ ∀ i, C3162.adjugate i i ≠ 0) := by
  intro h
  have := certificate3162
  rw [h.1] at this
  norm_num at this
def C3163 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3163 : C3163.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3163 : ¬ (C3163.det = 0 ∧ ∀ i, C3163.adjugate i i ≠ 0) := by
  intro h
  have := certificate3163
  rw [h.1] at this
  norm_num at this
def C3164 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3164 : C3164.det = (82 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3164 : ¬ (C3164.det = 0 ∧ ∀ i, C3164.adjugate i i ≠ 0) := by
  intro h
  have := certificate3164
  rw [h.1] at this
  norm_num at this
def C3165 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3165 : C3165.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3165 : ¬ (C3165.det = 0 ∧ ∀ i, C3165.adjugate i i ≠ 0) := by
  intro h
  have := certificate3165
  rw [h.1] at this
  norm_num at this
def C3166 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3166 : C3166.det = (45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3166 : ¬ (C3166.det = 0 ∧ ∀ i, C3166.adjugate i i ≠ 0) := by
  intro h
  have := certificate3166
  rw [h.1] at this
  norm_num at this
def C3167 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3167 : C3167.det = (113 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3167 : ¬ (C3167.det = 0 ∧ ∀ i, C3167.adjugate i i ≠ 0) := by
  intro h
  have := certificate3167
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0098
