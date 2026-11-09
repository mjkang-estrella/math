import VerifiedDet
namespace Nut8.NewCertificates0126
def C4032 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4032 : C4032.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4032 : ¬ (C4032.det = 0 ∧ ∀ i, C4032.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4032
def C4033 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4033 : C4033.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4033 : ¬ (C4033.det = 0 ∧ ∀ i, C4033.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4033
def C4034 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4034 : C4034.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4034 : ¬ (C4034.det = 0 ∧ ∀ i, C4034.adjugate i i ≠ 0) := by
  intro h
  have := certificate4034
  rw [h.1] at this
  norm_num at this
def C4035 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4035 : C4035.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4035 : ¬ (C4035.det = 0 ∧ ∀ i, C4035.adjugate i i ≠ 0) := by
  intro h
  have := certificate4035
  rw [h.1] at this
  norm_num at this
def C4036 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4036 : C4036.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4036 : ¬ (C4036.det = 0 ∧ ∀ i, C4036.adjugate i i ≠ 0) := by
  intro h
  have := certificate4036
  rw [h.1] at this
  norm_num at this
def C4037 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4037 : C4037.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4037 : ¬ (C4037.det = 0 ∧ ∀ i, C4037.adjugate i i ≠ 0) := by
  intro h
  have := certificate4037
  rw [h.1] at this
  norm_num at this
def C4038 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4038 : C4038.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4038 : ¬ (C4038.det = 0 ∧ ∀ i, C4038.adjugate i i ≠ 0) := by
  intro h
  have := certificate4038
  rw [h.1] at this
  norm_num at this
def C4039 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4039 : C4039.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4039 : ¬ (C4039.det = 0 ∧ ∀ i, C4039.adjugate i i ≠ 0) := by
  intro h
  have := certificate4039
  rw [h.1] at this
  norm_num at this
def C4040 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4040 : C4040.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4040 : ¬ (C4040.det = 0 ∧ ∀ i, C4040.adjugate i i ≠ 0) := by
  intro h
  have := certificate4040
  rw [h.1] at this
  norm_num at this
def C4041 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4041 : C4041.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4041 : ¬ (C4041.det = 0 ∧ ∀ i, C4041.adjugate i i ≠ 0) := by
  intro h
  have := certificate4041
  rw [h.1] at this
  norm_num at this
def C4042 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4042 : C4042.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4042 : ¬ (C4042.det = 0 ∧ ∀ i, C4042.adjugate i i ≠ 0) := by
  intro h
  have := certificate4042
  rw [h.1] at this
  norm_num at this
def C4043 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4043 : C4043.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4043 : ¬ (C4043.det = 0 ∧ ∀ i, C4043.adjugate i i ≠ 0) := by
  intro h
  have := certificate4043
  rw [h.1] at this
  norm_num at this
def C4044 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4044 : C4044.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4044 : ¬ (C4044.det = 0 ∧ ∀ i, C4044.adjugate i i ≠ 0) := by
  intro h
  have := certificate4044
  rw [h.1] at this
  norm_num at this
def C4045 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4045 : C4045.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4045 : ¬ (C4045.det = 0 ∧ ∀ i, C4045.adjugate i i ≠ 0) := by
  intro h
  have := certificate4045
  rw [h.1] at this
  norm_num at this
def C4046 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4046 : C4046.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4046 : ¬ (C4046.det = 0 ∧ ∀ i, C4046.adjugate i i ≠ 0) := by
  intro h
  have := certificate4046
  rw [h.1] at this
  norm_num at this
def C4047 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4047 : C4047.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4047 : ¬ (C4047.det = 0 ∧ ∀ i, C4047.adjugate i i ≠ 0) := by
  intro h
  have := certificate4047
  rw [h.1] at this
  norm_num at this
def C4048 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4048 : C4048.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4048 : ¬ (C4048.det = 0 ∧ ∀ i, C4048.adjugate i i ≠ 0) := by
  intro h
  have := certificate4048
  rw [h.1] at this
  norm_num at this
def C4049 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4049 : C4049.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4049 : ¬ (C4049.det = 0 ∧ ∀ i, C4049.adjugate i i ≠ 0) := by
  intro h
  have := certificate4049
  rw [h.1] at this
  norm_num at this
def C4050 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4050 : C4050.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4050 : ¬ (C4050.det = 0 ∧ ∀ i, C4050.adjugate i i ≠ 0) := by
  intro h
  have := certificate4050
  rw [h.1] at this
  norm_num at this
def C4051 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4051 : C4051.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4051 : ¬ (C4051.det = 0 ∧ ∀ i, C4051.adjugate i i ≠ 0) := by
  intro h
  have := certificate4051
  rw [h.1] at this
  norm_num at this
def C4052 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4052 : C4052.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4052 : ¬ (C4052.det = 0 ∧ ∀ i, C4052.adjugate i i ≠ 0) := by
  intro h
  have := certificate4052
  rw [h.1] at this
  norm_num at this
def C4053 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4053 : C4053.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4053 : ¬ (C4053.det = 0 ∧ ∀ i, C4053.adjugate i i ≠ 0) := by
  intro h
  have := certificate4053
  rw [h.1] at this
  norm_num at this
def C4054 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4054 : C4054.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4054 : ¬ (C4054.det = 0 ∧ ∀ i, C4054.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4054
def C4055 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4055 : C4055.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4055 : ¬ (C4055.det = 0 ∧ ∀ i, C4055.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4055
def C4056 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4056 : C4056.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4056 : ¬ (C4056.det = 0 ∧ ∀ i, C4056.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4056
def C4057 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4057 : C4057.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4057 : ¬ (C4057.det = 0 ∧ ∀ i, C4057.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4057
def C4058 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4058 : C4058.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4058 : ¬ (C4058.det = 0 ∧ ∀ i, C4058.adjugate i i ≠ 0) := by
  intro h
  have := certificate4058
  rw [h.1] at this
  norm_num at this
def C4059 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4059 : C4059.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4059 : ¬ (C4059.det = 0 ∧ ∀ i, C4059.adjugate i i ≠ 0) := by
  intro h
  have := certificate4059
  rw [h.1] at this
  norm_num at this
def C4060 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4060 : C4060.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4060 : ¬ (C4060.det = 0 ∧ ∀ i, C4060.adjugate i i ≠ 0) := by
  intro h
  have := certificate4060
  rw [h.1] at this
  norm_num at this
def C4061 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4061 : C4061.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4061 : ¬ (C4061.det = 0 ∧ ∀ i, C4061.adjugate i i ≠ 0) := by
  intro h
  have := certificate4061
  rw [h.1] at this
  norm_num at this
def C4062 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4062 : C4062.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4062 : ¬ (C4062.det = 0 ∧ ∀ i, C4062.adjugate i i ≠ 0) := by
  intro h
  have := certificate4062
  rw [h.1] at this
  norm_num at this
def C4063 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4063 : C4063.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4063 : ¬ (C4063.det = 0 ∧ ∀ i, C4063.adjugate i i ≠ 0) := by
  intro h
  have := certificate4063
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0126
