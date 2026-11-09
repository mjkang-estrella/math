import VerifiedDet
namespace Nut8.NewCertificates0129
def C4128 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4128 : C4128.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4128 : ¬ (C4128.det = 0 ∧ ∀ i, C4128.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4128
def C4129 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4129 : C4129.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4129 : ¬ (C4129.det = 0 ∧ ∀ i, C4129.adjugate i i ≠ 0) := by
  intro h
  have := certificate4129
  rw [h.1] at this
  norm_num at this
def C4130 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4130 : C4130.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4130 : ¬ (C4130.det = 0 ∧ ∀ i, C4130.adjugate i i ≠ 0) := by
  intro h
  have := certificate4130
  rw [h.1] at this
  norm_num at this
def C4131 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4131 : C4131.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4131 : ¬ (C4131.det = 0 ∧ ∀ i, C4131.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4131
def C4132 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4132 : C4132.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4132 : ¬ (C4132.det = 0 ∧ ∀ i, C4132.adjugate i i ≠ 0) := by
  intro h
  have := certificate4132
  rw [h.1] at this
  norm_num at this
def C4133 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4133 : C4133.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4133 : ¬ (C4133.det = 0 ∧ ∀ i, C4133.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4133
def C4134 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4134 : C4134.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4134 : ¬ (C4134.det = 0 ∧ ∀ i, C4134.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4134
def C4135 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4135 : C4135.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4135 : ¬ (C4135.det = 0 ∧ ∀ i, C4135.adjugate i i ≠ 0) := by
  intro h
  have := certificate4135
  rw [h.1] at this
  norm_num at this
def C4136 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4136 : C4136.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4136 : ¬ (C4136.det = 0 ∧ ∀ i, C4136.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4136
def C4137 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4137 : C4137.det = (-72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4137 : ¬ (C4137.det = 0 ∧ ∀ i, C4137.adjugate i i ≠ 0) := by
  intro h
  have := certificate4137
  rw [h.1] at this
  norm_num at this
def C4138 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4138 : C4138.det = (-72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4138 : ¬ (C4138.det = 0 ∧ ∀ i, C4138.adjugate i i ≠ 0) := by
  intro h
  have := certificate4138
  rw [h.1] at this
  norm_num at this
def C4139 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4139 : C4139.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4139 : ¬ (C4139.det = 0 ∧ ∀ i, C4139.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4139
def C4140 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4140 : C4140.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4140 : ¬ (C4140.det = 0 ∧ ∀ i, C4140.adjugate i i ≠ 0) := by
  intro h
  have := certificate4140
  rw [h.1] at this
  norm_num at this
def C4141 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4141 : C4141.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4141 : ¬ (C4141.det = 0 ∧ ∀ i, C4141.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4141
def C4142 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4142 : C4142.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4142 : ¬ (C4142.det = 0 ∧ ∀ i, C4142.adjugate i i ≠ 0) := by
  intro h
  have := certificate4142
  rw [h.1] at this
  norm_num at this
def C4143 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4143 : C4143.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4143 : ¬ (C4143.det = 0 ∧ ∀ i, C4143.adjugate i i ≠ 0) := by
  intro h
  have := certificate4143
  rw [h.1] at this
  norm_num at this
def C4144 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4144 : C4144.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4144 : ¬ (C4144.det = 0 ∧ ∀ i, C4144.adjugate i i ≠ 0) := by
  intro h
  have := certificate4144
  rw [h.1] at this
  norm_num at this
def C4145 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4145 : C4145.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4145 : ¬ (C4145.det = 0 ∧ ∀ i, C4145.adjugate i i ≠ 0) := by
  intro h
  have := certificate4145
  rw [h.1] at this
  norm_num at this
def C4146 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4146 : C4146.det = (88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4146 : ¬ (C4146.det = 0 ∧ ∀ i, C4146.adjugate i i ≠ 0) := by
  intro h
  have := certificate4146
  rw [h.1] at this
  norm_num at this
def C4147 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4147 : C4147.det = (-56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4147 : ¬ (C4147.det = 0 ∧ ∀ i, C4147.adjugate i i ≠ 0) := by
  intro h
  have := certificate4147
  rw [h.1] at this
  norm_num at this
def C4148 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4148 : C4148.det = (-56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4148 : ¬ (C4148.det = 0 ∧ ∀ i, C4148.adjugate i i ≠ 0) := by
  intro h
  have := certificate4148
  rw [h.1] at this
  norm_num at this
def C4149 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 2, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4149 : C4149.det = (88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4149 : ¬ (C4149.det = 0 ∧ ∀ i, C4149.adjugate i i ≠ 0) := by
  intro h
  have := certificate4149
  rw [h.1] at this
  norm_num at this
def C4150 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate4150 : C4150.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4150 : ¬ (C4150.det = 0 ∧ ∀ i, C4150.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4150
def C4151 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate4151 : C4151.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4151 : ¬ (C4151.det = 0 ∧ ∀ i, C4151.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4151
def C4152 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate4152 : C4152.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4152 : ¬ (C4152.det = 0 ∧ ∀ i, C4152.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4152
def C4153 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate4153 : C4153.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4153 : ¬ (C4153.det = 0 ∧ ∀ i, C4153.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4153
def C4154 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate4154 : C4154.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4154 : ¬ (C4154.det = 0 ∧ ∀ i, C4154.adjugate i i ≠ 0) := by
  intro h
  have := certificate4154
  rw [h.1] at this
  norm_num at this
def C4155 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate4155 : C4155.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4155 : ¬ (C4155.det = 0 ∧ ∀ i, C4155.adjugate i i ≠ 0) := by
  intro h
  have := certificate4155
  rw [h.1] at this
  norm_num at this
def C4156 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate4156 : C4156.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4156 : ¬ (C4156.det = 0 ∧ ∀ i, C4156.adjugate i i ≠ 0) := by
  intro h
  have := certificate4156
  rw [h.1] at this
  norm_num at this
def C4157 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate4157 : C4157.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4157 : ¬ (C4157.det = 0 ∧ ∀ i, C4157.adjugate i i ≠ 0) := by
  intro h
  have := certificate4157
  rw [h.1] at this
  norm_num at this
def C4158 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate4158 : C4158.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4158 : ¬ (C4158.det = 0 ∧ ∀ i, C4158.adjugate i i ≠ 0) := by
  intro h
  have := certificate4158
  rw [h.1] at this
  norm_num at this
def C4159 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate4159 : C4159.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4159 : ¬ (C4159.det = 0 ∧ ∀ i, C4159.adjugate i i ≠ 0) := by
  intro h
  have := certificate4159
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0129
