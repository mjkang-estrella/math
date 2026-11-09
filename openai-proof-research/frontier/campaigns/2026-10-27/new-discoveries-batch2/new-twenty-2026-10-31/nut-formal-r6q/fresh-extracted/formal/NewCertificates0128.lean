import VerifiedDet
namespace Nut8.NewCertificates0128
def C4096 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4096 : C4096.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4096 : ¬ (C4096.det = 0 ∧ ∀ i, C4096.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4096
def C4097 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4097 : C4097.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4097 : ¬ (C4097.det = 0 ∧ ∀ i, C4097.adjugate i i ≠ 0) := by
  intro h
  have := certificate4097
  rw [h.1] at this
  norm_num at this
def C4098 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4098 : C4098.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4098 : ¬ (C4098.det = 0 ∧ ∀ i, C4098.adjugate i i ≠ 0) := by
  intro h
  have := certificate4098
  rw [h.1] at this
  norm_num at this
def C4099 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4099 : C4099.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4099 : ¬ (C4099.det = 0 ∧ ∀ i, C4099.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4099
def C4100 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4100 : C4100.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4100 : ¬ (C4100.det = 0 ∧ ∀ i, C4100.adjugate i i ≠ 0) := by
  intro h
  have := certificate4100
  rw [h.1] at this
  norm_num at this
def C4101 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4101 : C4101.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4101 : ¬ (C4101.det = 0 ∧ ∀ i, C4101.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4101
def C4102 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4102 : C4102.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4102 : ¬ (C4102.det = 0 ∧ ∀ i, C4102.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4102
def C4103 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4103 : C4103.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4103 : ¬ (C4103.det = 0 ∧ ∀ i, C4103.adjugate i i ≠ 0) := by
  intro h
  have := certificate4103
  rw [h.1] at this
  norm_num at this
def C4104 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4104 : C4104.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4104 : ¬ (C4104.det = 0 ∧ ∀ i, C4104.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4104
def C4105 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4105 : C4105.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4105 : ¬ (C4105.det = 0 ∧ ∀ i, C4105.adjugate i i ≠ 0) := by
  intro h
  have := certificate4105
  rw [h.1] at this
  norm_num at this
def C4106 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4106 : C4106.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4106 : ¬ (C4106.det = 0 ∧ ∀ i, C4106.adjugate i i ≠ 0) := by
  intro h
  have := certificate4106
  rw [h.1] at this
  norm_num at this
def C4107 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4107 : C4107.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4107 : ¬ (C4107.det = 0 ∧ ∀ i, C4107.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4107
def C4108 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4108 : C4108.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4108 : ¬ (C4108.det = 0 ∧ ∀ i, C4108.adjugate i i ≠ 0) := by
  intro h
  have := certificate4108
  rw [h.1] at this
  norm_num at this
def C4109 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4109 : C4109.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4109 : ¬ (C4109.det = 0 ∧ ∀ i, C4109.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4109
def C4110 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4110 : C4110.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4110 : ¬ (C4110.det = 0 ∧ ∀ i, C4110.adjugate i i ≠ 0) := by
  intro h
  have := certificate4110
  rw [h.1] at this
  norm_num at this
def C4111 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4111 : C4111.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4111 : ¬ (C4111.det = 0 ∧ ∀ i, C4111.adjugate i i ≠ 0) := by
  intro h
  have := certificate4111
  rw [h.1] at this
  norm_num at this
def C4112 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4112 : C4112.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4112 : ¬ (C4112.det = 0 ∧ ∀ i, C4112.adjugate i i ≠ 0) := by
  intro h
  have := certificate4112
  rw [h.1] at this
  norm_num at this
def C4113 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4113 : C4113.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4113 : ¬ (C4113.det = 0 ∧ ∀ i, C4113.adjugate i i ≠ 0) := by
  intro h
  have := certificate4113
  rw [h.1] at this
  norm_num at this
def C4114 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4114 : C4114.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4114 : ¬ (C4114.det = 0 ∧ ∀ i, C4114.adjugate i i ≠ 0) := by
  intro h
  have := certificate4114
  rw [h.1] at this
  norm_num at this
def C4115 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4115 : C4115.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4115 : ¬ (C4115.det = 0 ∧ ∀ i, C4115.adjugate i i ≠ 0) := by
  intro h
  have := certificate4115
  rw [h.1] at this
  norm_num at this
def C4116 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4116 : C4116.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4116 : ¬ (C4116.det = 0 ∧ ∀ i, C4116.adjugate i i ≠ 0) := by
  intro h
  have := certificate4116
  rw [h.1] at this
  norm_num at this
def C4117 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4117 : C4117.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4117 : ¬ (C4117.det = 0 ∧ ∀ i, C4117.adjugate i i ≠ 0) := by
  intro h
  have := certificate4117
  rw [h.1] at this
  norm_num at this
def C4118 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4118 : C4118.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4118 : ¬ (C4118.det = 0 ∧ ∀ i, C4118.adjugate i i ≠ 0) := by
  intro h
  have := certificate4118
  rw [h.1] at this
  norm_num at this
def C4119 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4119 : C4119.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4119 : ¬ (C4119.det = 0 ∧ ∀ i, C4119.adjugate i i ≠ 0) := by
  intro h
  have := certificate4119
  rw [h.1] at this
  norm_num at this
def C4120 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4120 : C4120.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4120 : ¬ (C4120.det = 0 ∧ ∀ i, C4120.adjugate i i ≠ 0) := by
  intro h
  have := certificate4120
  rw [h.1] at this
  norm_num at this
def C4121 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4121 : C4121.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4121 : ¬ (C4121.det = 0 ∧ ∀ i, C4121.adjugate i i ≠ 0) := by
  intro h
  have := certificate4121
  rw [h.1] at this
  norm_num at this
def C4122 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4122 : C4122.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4122 : ¬ (C4122.det = 0 ∧ ∀ i, C4122.adjugate i i ≠ 0) := by
  intro h
  have := certificate4122
  rw [h.1] at this
  norm_num at this
def C4123 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4123 : C4123.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4123 : ¬ (C4123.det = 0 ∧ ∀ i, C4123.adjugate i i ≠ 0) := by
  intro h
  have := certificate4123
  rw [h.1] at this
  norm_num at this
def C4124 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4124 : C4124.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4124 : ¬ (C4124.det = 0 ∧ ∀ i, C4124.adjugate i i ≠ 0) := by
  intro h
  have := certificate4124
  rw [h.1] at this
  norm_num at this
def C4125 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4125 : C4125.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4125 : ¬ (C4125.det = 0 ∧ ∀ i, C4125.adjugate i i ≠ 0) := by
  intro h
  have := certificate4125
  rw [h.1] at this
  norm_num at this
def C4126 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4126 : C4126.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4126 : ¬ (C4126.det = 0 ∧ ∀ i, C4126.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4126
def C4127 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4127 : C4127.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4127 : ¬ (C4127.det = 0 ∧ ∀ i, C4127.adjugate i i ≠ 0) := by
  intro h
  have := certificate4127
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0128
