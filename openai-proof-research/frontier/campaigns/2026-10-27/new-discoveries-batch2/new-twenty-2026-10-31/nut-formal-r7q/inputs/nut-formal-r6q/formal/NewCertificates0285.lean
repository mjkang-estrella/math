import VerifiedDet
namespace Nut8.NewCertificates0285
def C9120 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9120 : C9120.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9120 : ¬ (C9120.det = 0 ∧ ∀ i, C9120.adjugate i i ≠ 0) := by
  intro h
  have := certificate9120
  rw [h.1] at this
  norm_num at this
def C9121 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9121 : C9121.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9121 : ¬ (C9121.det = 0 ∧ ∀ i, C9121.adjugate i i ≠ 0) := by
  intro h
  have := certificate9121
  rw [h.1] at this
  norm_num at this
def C9122 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9122 : C9122.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9122 : ¬ (C9122.det = 0 ∧ ∀ i, C9122.adjugate i i ≠ 0) := by
  intro h
  have := certificate9122
  rw [h.1] at this
  norm_num at this
def C9123 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9123 : C9123.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9123 : ¬ (C9123.det = 0 ∧ ∀ i, C9123.adjugate i i ≠ 0) := by
  intro h
  have := certificate9123
  rw [h.1] at this
  norm_num at this
def C9124 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9124 : C9124.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9124 : ¬ (C9124.det = 0 ∧ ∀ i, C9124.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9124
def C9125 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9125 : C9125.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9125 : ¬ (C9125.det = 0 ∧ ∀ i, C9125.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9125
def C9126 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9126 : C9126.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9126 : ¬ (C9126.det = 0 ∧ ∀ i, C9126.adjugate i i ≠ 0) := by
  intro h
  have := certificate9126
  rw [h.1] at this
  norm_num at this
def C9127 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9127 : C9127.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9127 : ¬ (C9127.det = 0 ∧ ∀ i, C9127.adjugate i i ≠ 0) := by
  intro h
  have := certificate9127
  rw [h.1] at this
  norm_num at this
def C9128 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9128 : C9128.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9128 : ¬ (C9128.det = 0 ∧ ∀ i, C9128.adjugate i i ≠ 0) := by
  intro h
  have := certificate9128
  rw [h.1] at this
  norm_num at this
def C9129 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9129 : C9129.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9129 : ¬ (C9129.det = 0 ∧ ∀ i, C9129.adjugate i i ≠ 0) := by
  intro h
  have := certificate9129
  rw [h.1] at this
  norm_num at this
def C9130 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9130 : C9130.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9130 : ¬ (C9130.det = 0 ∧ ∀ i, C9130.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9130
def C9131 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9131 : C9131.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9131 : ¬ (C9131.det = 0 ∧ ∀ i, C9131.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9131
def C9132 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9132 : C9132.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9132 : ¬ (C9132.det = 0 ∧ ∀ i, C9132.adjugate i i ≠ 0) := by
  intro h
  have := certificate9132
  rw [h.1] at this
  norm_num at this
def C9133 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9133 : C9133.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9133 : ¬ (C9133.det = 0 ∧ ∀ i, C9133.adjugate i i ≠ 0) := by
  intro h
  have := certificate9133
  rw [h.1] at this
  norm_num at this
def C9134 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9134 : C9134.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9134 : ¬ (C9134.det = 0 ∧ ∀ i, C9134.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9134
def C9135 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9135 : C9135.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9135 : ¬ (C9135.det = 0 ∧ ∀ i, C9135.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9135
def C9136 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9136 : C9136.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9136 : ¬ (C9136.det = 0 ∧ ∀ i, C9136.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9136
def C9137 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9137 : C9137.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9137 : ¬ (C9137.det = 0 ∧ ∀ i, C9137.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9137
def C9138 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9138 : C9138.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9138 : ¬ (C9138.det = 0 ∧ ∀ i, C9138.adjugate i i ≠ 0) := by
  intro h
  have := certificate9138
  rw [h.1] at this
  norm_num at this
def C9139 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9139 : C9139.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9139 : ¬ (C9139.det = 0 ∧ ∀ i, C9139.adjugate i i ≠ 0) := by
  intro h
  have := certificate9139
  rw [h.1] at this
  norm_num at this
def C9140 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9140 : C9140.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9140 : ¬ (C9140.det = 0 ∧ ∀ i, C9140.adjugate i i ≠ 0) := by
  intro h
  have := certificate9140
  rw [h.1] at this
  norm_num at this
def C9141 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9141 : C9141.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9141 : ¬ (C9141.det = 0 ∧ ∀ i, C9141.adjugate i i ≠ 0) := by
  intro h
  have := certificate9141
  rw [h.1] at this
  norm_num at this
def C9142 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9142 : C9142.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9142 : ¬ (C9142.det = 0 ∧ ∀ i, C9142.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9142
def C9143 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9143 : C9143.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9143 : ¬ (C9143.det = 0 ∧ ∀ i, C9143.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9143
def C9144 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9144 : C9144.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9144 : ¬ (C9144.det = 0 ∧ ∀ i, C9144.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9144
def C9145 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate9145 : C9145.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9145 : ¬ (C9145.det = 0 ∧ ∀ i, C9145.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9145
def C9146 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9146 : C9146.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9146 : ¬ (C9146.det = 0 ∧ ∀ i, C9146.adjugate i i ≠ 0) := by
  intro h
  have := certificate9146
  rw [h.1] at this
  norm_num at this
def C9147 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate9147 : C9147.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9147 : ¬ (C9147.det = 0 ∧ ∀ i, C9147.adjugate i i ≠ 0) := by
  intro h
  have := certificate9147
  rw [h.1] at this
  norm_num at this
def C9148 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9148 : C9148.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9148 : ¬ (C9148.det = 0 ∧ ∀ i, C9148.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9148
def C9149 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate9149 : C9149.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9149 : ¬ (C9149.det = 0 ∧ ∀ i, C9149.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9149
def C9150 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9150 : C9150.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9150 : ¬ (C9150.det = 0 ∧ ∀ i, C9150.adjugate i i ≠ 0) := by
  intro h
  have := certificate9150
  rw [h.1] at this
  norm_num at this
def C9151 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, -1, 0]
theorem certificate9151 : C9151.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9151 : ¬ (C9151.det = 0 ∧ ∀ i, C9151.adjugate i i ≠ 0) := by
  intro h
  have := certificate9151
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0285
