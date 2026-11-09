import VerifiedDet
namespace Nut8.NewCertificates0223
def C7136 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7136 : C7136.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7136 : ¬ (C7136.det = 0 ∧ ∀ i, C7136.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7136
def C7137 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7137 : C7137.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7137 : ¬ (C7137.det = 0 ∧ ∀ i, C7137.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7137
def C7138 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7138 : C7138.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7138 : ¬ (C7138.det = 0 ∧ ∀ i, C7138.adjugate i i ≠ 0) := by
  intro h
  have := certificate7138
  rw [h.1] at this
  norm_num at this
def C7139 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7139 : C7139.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7139 : ¬ (C7139.det = 0 ∧ ∀ i, C7139.adjugate i i ≠ 0) := by
  intro h
  have := certificate7139
  rw [h.1] at this
  norm_num at this
def C7140 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate7140 : C7140.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7140 : ¬ (C7140.det = 0 ∧ ∀ i, C7140.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7140
def C7141 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate7141 : C7141.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7141 : ¬ (C7141.det = 0 ∧ ∀ i, C7141.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7141
def C7142 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate7142 : C7142.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7142 : ¬ (C7142.det = 0 ∧ ∀ i, C7142.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7142
def C7143 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate7143 : C7143.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7143 : ¬ (C7143.det = 0 ∧ ∀ i, C7143.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7143
def C7144 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate7144 : C7144.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7144 : ¬ (C7144.det = 0 ∧ ∀ i, C7144.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7144
def C7145 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate7145 : C7145.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7145 : ¬ (C7145.det = 0 ∧ ∀ i, C7145.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7145
def C7146 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate7146 : C7146.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7146 : ¬ (C7146.det = 0 ∧ ∀ i, C7146.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7146
def C7147 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate7147 : C7147.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7147 : ¬ (C7147.det = 0 ∧ ∀ i, C7147.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7147
def C7148 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate7148 : C7148.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7148 : ¬ (C7148.det = 0 ∧ ∀ i, C7148.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7148
def C7149 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate7149 : C7149.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7149 : ¬ (C7149.det = 0 ∧ ∀ i, C7149.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7149
def C7150 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate7150 : C7150.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7150 : ¬ (C7150.det = 0 ∧ ∀ i, C7150.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7150
def C7151 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate7151 : C7151.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7151 : ¬ (C7151.det = 0 ∧ ∀ i, C7151.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7151
def C7152 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate7152 : C7152.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7152 : ¬ (C7152.det = 0 ∧ ∀ i, C7152.adjugate i i ≠ 0) := by
  intro h
  have := certificate7152
  rw [h.1] at this
  norm_num at this
def C7153 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate7153 : C7153.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7153 : ¬ (C7153.det = 0 ∧ ∀ i, C7153.adjugate i i ≠ 0) := by
  intro h
  have := certificate7153
  rw [h.1] at this
  norm_num at this
def C7154 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate7154 : C7154.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7154 : ¬ (C7154.det = 0 ∧ ∀ i, C7154.adjugate i i ≠ 0) := by
  intro h
  have := certificate7154
  rw [h.1] at this
  norm_num at this
def C7155 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate7155 : C7155.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7155 : ¬ (C7155.det = 0 ∧ ∀ i, C7155.adjugate i i ≠ 0) := by
  intro h
  have := certificate7155
  rw [h.1] at this
  norm_num at this
def C7156 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7156 : C7156.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7156 : ¬ (C7156.det = 0 ∧ ∀ i, C7156.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7156
def C7157 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7157 : C7157.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7157 : ¬ (C7157.det = 0 ∧ ∀ i, C7157.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7157
def C7158 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7158 : C7158.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7158 : ¬ (C7158.det = 0 ∧ ∀ i, C7158.adjugate i i ≠ 0) := by
  intro h
  have := certificate7158
  rw [h.1] at this
  norm_num at this
def C7159 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7159 : C7159.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7159 : ¬ (C7159.det = 0 ∧ ∀ i, C7159.adjugate i i ≠ 0) := by
  intro h
  have := certificate7159
  rw [h.1] at this
  norm_num at this
def C7160 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7160 : C7160.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7160 : ¬ (C7160.det = 0 ∧ ∀ i, C7160.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7160
def C7161 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7161 : C7161.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7161 : ¬ (C7161.det = 0 ∧ ∀ i, C7161.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7161
def C7162 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7162 : C7162.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7162 : ¬ (C7162.det = 0 ∧ ∀ i, C7162.adjugate i i ≠ 0) := by
  intro h
  have := certificate7162
  rw [h.1] at this
  norm_num at this
def C7163 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -2, 0, 0, 0]
theorem certificate7163 : C7163.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7163 : ¬ (C7163.det = 0 ∧ ∀ i, C7163.adjugate i i ≠ 0) := by
  intro h
  have := certificate7163
  rw [h.1] at this
  norm_num at this
def C7164 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7164 : C7164.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7164 : ¬ (C7164.det = 0 ∧ ∀ i, C7164.adjugate i i ≠ 0) := by
  intro h
  have := certificate7164
  rw [h.1] at this
  norm_num at this
def C7165 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7165 : C7165.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7165 : ¬ (C7165.det = 0 ∧ ∀ i, C7165.adjugate i i ≠ 0) := by
  intro h
  have := certificate7165
  rw [h.1] at this
  norm_num at this
def C7166 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7166 : C7166.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7166 : ¬ (C7166.det = 0 ∧ ∀ i, C7166.adjugate i i ≠ 0) := by
  intro h
  have := certificate7166
  rw [h.1] at this
  norm_num at this
def C7167 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0]
theorem certificate7167 : C7167.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7167 : ¬ (C7167.det = 0 ∧ ∀ i, C7167.adjugate i i ≠ 0) := by
  intro h
  have := certificate7167
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0223
