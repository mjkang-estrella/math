import VerifiedDet
namespace Nut8.NewCertificates0283
def C9056 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9056 : C9056.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9056 : ¬ (C9056.det = 0 ∧ ∀ i, C9056.adjugate i i ≠ 0) := by
  intro h
  have := certificate9056
  rw [h.1] at this
  norm_num at this
def C9057 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9057 : C9057.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9057 : ¬ (C9057.det = 0 ∧ ∀ i, C9057.adjugate i i ≠ 0) := by
  intro h
  have := certificate9057
  rw [h.1] at this
  norm_num at this
def C9058 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9058 : C9058.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9058 : ¬ (C9058.det = 0 ∧ ∀ i, C9058.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9058
def C9059 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9059 : C9059.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9059 : ¬ (C9059.det = 0 ∧ ∀ i, C9059.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9059
def C9060 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9060 : C9060.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9060 : ¬ (C9060.det = 0 ∧ ∀ i, C9060.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9060
def C9061 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9061 : C9061.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9061 : ¬ (C9061.det = 0 ∧ ∀ i, C9061.adjugate i i ≠ 0) := by
  intro h
  have := certificate9061
  rw [h.1] at this
  norm_num at this
def C9062 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9062 : C9062.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9062 : ¬ (C9062.det = 0 ∧ ∀ i, C9062.adjugate i i ≠ 0) := by
  intro h
  have := certificate9062
  rw [h.1] at this
  norm_num at this
def C9063 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9063 : C9063.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9063 : ¬ (C9063.det = 0 ∧ ∀ i, C9063.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9063
def C9064 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9064 : C9064.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9064 : ¬ (C9064.det = 0 ∧ ∀ i, C9064.adjugate i i ≠ 0) := by
  intro h
  have := certificate9064
  rw [h.1] at this
  norm_num at this
def C9065 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9065 : C9065.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9065 : ¬ (C9065.det = 0 ∧ ∀ i, C9065.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9065
def C9066 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9066 : C9066.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9066 : ¬ (C9066.det = 0 ∧ ∀ i, C9066.adjugate i i ≠ 0) := by
  intro h
  have := certificate9066
  rw [h.1] at this
  norm_num at this
def C9067 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9067 : C9067.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9067 : ¬ (C9067.det = 0 ∧ ∀ i, C9067.adjugate i i ≠ 0) := by
  intro h
  have := certificate9067
  rw [h.1] at this
  norm_num at this
def C9068 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9068 : C9068.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9068 : ¬ (C9068.det = 0 ∧ ∀ i, C9068.adjugate i i ≠ 0) := by
  intro h
  have := certificate9068
  rw [h.1] at this
  norm_num at this
def C9069 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9069 : C9069.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9069 : ¬ (C9069.det = 0 ∧ ∀ i, C9069.adjugate i i ≠ 0) := by
  intro h
  have := certificate9069
  rw [h.1] at this
  norm_num at this
def C9070 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9070 : C9070.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9070 : ¬ (C9070.det = 0 ∧ ∀ i, C9070.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9070
def C9071 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9071 : C9071.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9071 : ¬ (C9071.det = 0 ∧ ∀ i, C9071.adjugate i i ≠ 0) := by
  intro h
  have := certificate9071
  rw [h.1] at this
  norm_num at this
def C9072 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9072 : C9072.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9072 : ¬ (C9072.det = 0 ∧ ∀ i, C9072.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9072
def C9073 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9073 : C9073.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9073 : ¬ (C9073.det = 0 ∧ ∀ i, C9073.adjugate i i ≠ 0) := by
  intro h
  have := certificate9073
  rw [h.1] at this
  norm_num at this
def C9074 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9074 : C9074.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9074 : ¬ (C9074.det = 0 ∧ ∀ i, C9074.adjugate i i ≠ 0) := by
  intro h
  have := certificate9074
  rw [h.1] at this
  norm_num at this
def C9075 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9075 : C9075.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9075 : ¬ (C9075.det = 0 ∧ ∀ i, C9075.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9075
def C9076 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9076 : C9076.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9076 : ¬ (C9076.det = 0 ∧ ∀ i, C9076.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9076
def C9077 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9077 : C9077.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9077 : ¬ (C9077.det = 0 ∧ ∀ i, C9077.adjugate i i ≠ 0) := by
  intro h
  have := certificate9077
  rw [h.1] at this
  norm_num at this
def C9078 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9078 : C9078.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9078 : ¬ (C9078.det = 0 ∧ ∀ i, C9078.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9078
def C9079 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9079 : C9079.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9079 : ¬ (C9079.det = 0 ∧ ∀ i, C9079.adjugate i i ≠ 0) := by
  intro h
  have := certificate9079
  rw [h.1] at this
  norm_num at this
def C9080 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9080 : C9080.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9080 : ¬ (C9080.det = 0 ∧ ∀ i, C9080.adjugate i i ≠ 0) := by
  intro h
  have := certificate9080
  rw [h.1] at this
  norm_num at this
def C9081 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9081 : C9081.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9081 : ¬ (C9081.det = 0 ∧ ∀ i, C9081.adjugate i i ≠ 0) := by
  intro h
  have := certificate9081
  rw [h.1] at this
  norm_num at this
def C9082 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9082 : C9082.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9082 : ¬ (C9082.det = 0 ∧ ∀ i, C9082.adjugate i i ≠ 0) := by
  intro h
  have := certificate9082
  rw [h.1] at this
  norm_num at this
def C9083 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9083 : C9083.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9083 : ¬ (C9083.det = 0 ∧ ∀ i, C9083.adjugate i i ≠ 0) := by
  intro h
  have := certificate9083
  rw [h.1] at this
  norm_num at this
def C9084 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9084 : C9084.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9084 : ¬ (C9084.det = 0 ∧ ∀ i, C9084.adjugate i i ≠ 0) := by
  intro h
  have := certificate9084
  rw [h.1] at this
  norm_num at this
def C9085 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9085 : C9085.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9085 : ¬ (C9085.det = 0 ∧ ∀ i, C9085.adjugate i i ≠ 0) := by
  intro h
  have := certificate9085
  rw [h.1] at this
  norm_num at this
def C9086 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9086 : C9086.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9086 : ¬ (C9086.det = 0 ∧ ∀ i, C9086.adjugate i i ≠ 0) := by
  intro h
  have := certificate9086
  rw [h.1] at this
  norm_num at this
def C9087 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9087 : C9087.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9087 : ¬ (C9087.det = 0 ∧ ∀ i, C9087.adjugate i i ≠ 0) := by
  intro h
  have := certificate9087
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0283
