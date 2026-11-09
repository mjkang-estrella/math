import VerifiedDet
namespace Nut8.NewCertificates0221
def C7072 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7072 : C7072.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7072 : ¬ (C7072.det = 0 ∧ ∀ i, C7072.adjugate i i ≠ 0) := by
  intro h
  have := certificate7072
  rw [h.1] at this
  norm_num at this
def C7073 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7073 : C7073.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7073 : ¬ (C7073.det = 0 ∧ ∀ i, C7073.adjugate i i ≠ 0) := by
  intro h
  have := certificate7073
  rw [h.1] at this
  norm_num at this
def C7074 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7074 : C7074.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7074 : ¬ (C7074.det = 0 ∧ ∀ i, C7074.adjugate i i ≠ 0) := by
  intro h
  have := certificate7074
  rw [h.1] at this
  norm_num at this
def C7075 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7075 : C7075.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7075 : ¬ (C7075.det = 0 ∧ ∀ i, C7075.adjugate i i ≠ 0) := by
  intro h
  have := certificate7075
  rw [h.1] at this
  norm_num at this
def C7076 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7076 : C7076.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7076 : ¬ (C7076.det = 0 ∧ ∀ i, C7076.adjugate i i ≠ 0) := by
  intro h
  have := certificate7076
  rw [h.1] at this
  norm_num at this
def C7077 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7077 : C7077.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7077 : ¬ (C7077.det = 0 ∧ ∀ i, C7077.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7077
def C7078 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7078 : C7078.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7078 : ¬ (C7078.det = 0 ∧ ∀ i, C7078.adjugate i i ≠ 0) := by
  intro h
  have := certificate7078
  rw [h.1] at this
  norm_num at this
def C7079 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7079 : C7079.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7079 : ¬ (C7079.det = 0 ∧ ∀ i, C7079.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7079
def C7080 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7080 : C7080.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7080 : ¬ (C7080.det = 0 ∧ ∀ i, C7080.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7080
def C7081 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7081 : C7081.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7081 : ¬ (C7081.det = 0 ∧ ∀ i, C7081.adjugate i i ≠ 0) := by
  intro h
  have := certificate7081
  rw [h.1] at this
  norm_num at this
def C7082 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7082 : C7082.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7082 : ¬ (C7082.det = 0 ∧ ∀ i, C7082.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7082
def C7083 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7083 : C7083.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7083 : ¬ (C7083.det = 0 ∧ ∀ i, C7083.adjugate i i ≠ 0) := by
  intro h
  have := certificate7083
  rw [h.1] at this
  norm_num at this
def C7084 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7084 : C7084.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7084 : ¬ (C7084.det = 0 ∧ ∀ i, C7084.adjugate i i ≠ 0) := by
  intro h
  have := certificate7084
  rw [h.1] at this
  norm_num at this
def C7085 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7085 : C7085.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7085 : ¬ (C7085.det = 0 ∧ ∀ i, C7085.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7085
def C7086 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7086 : C7086.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7086 : ¬ (C7086.det = 0 ∧ ∀ i, C7086.adjugate i i ≠ 0) := by
  intro h
  have := certificate7086
  rw [h.1] at this
  norm_num at this
def C7087 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7087 : C7087.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7087 : ¬ (C7087.det = 0 ∧ ∀ i, C7087.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7087
def C7088 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7088 : C7088.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7088 : ¬ (C7088.det = 0 ∧ ∀ i, C7088.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7088
def C7089 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7089 : C7089.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7089 : ¬ (C7089.det = 0 ∧ ∀ i, C7089.adjugate i i ≠ 0) := by
  intro h
  have := certificate7089
  rw [h.1] at this
  norm_num at this
def C7090 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7090 : C7090.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7090 : ¬ (C7090.det = 0 ∧ ∀ i, C7090.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7090
def C7091 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7091 : C7091.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7091 : ¬ (C7091.det = 0 ∧ ∀ i, C7091.adjugate i i ≠ 0) := by
  intro h
  have := certificate7091
  rw [h.1] at this
  norm_num at this
def C7092 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7092 : C7092.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7092 : ¬ (C7092.det = 0 ∧ ∀ i, C7092.adjugate i i ≠ 0) := by
  intro h
  have := certificate7092
  rw [h.1] at this
  norm_num at this
def C7093 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7093 : C7093.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7093 : ¬ (C7093.det = 0 ∧ ∀ i, C7093.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7093
def C7094 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7094 : C7094.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7094 : ¬ (C7094.det = 0 ∧ ∀ i, C7094.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7094
def C7095 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7095 : C7095.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7095 : ¬ (C7095.det = 0 ∧ ∀ i, C7095.adjugate i i ≠ 0) := by
  intro h
  have := certificate7095
  rw [h.1] at this
  norm_num at this
def C7096 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7096 : C7096.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7096 : ¬ (C7096.det = 0 ∧ ∀ i, C7096.adjugate i i ≠ 0) := by
  intro h
  have := certificate7096
  rw [h.1] at this
  norm_num at this
def C7097 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7097 : C7097.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7097 : ¬ (C7097.det = 0 ∧ ∀ i, C7097.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7097
def C7098 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7098 : C7098.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7098 : ¬ (C7098.det = 0 ∧ ∀ i, C7098.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7098
def C7099 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7099 : C7099.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7099 : ¬ (C7099.det = 0 ∧ ∀ i, C7099.adjugate i i ≠ 0) := by
  intro h
  have := certificate7099
  rw [h.1] at this
  norm_num at this
def C7100 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7100 : C7100.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7100 : ¬ (C7100.det = 0 ∧ ∀ i, C7100.adjugate i i ≠ 0) := by
  intro h
  have := certificate7100
  rw [h.1] at this
  norm_num at this
def C7101 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7101 : C7101.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7101 : ¬ (C7101.det = 0 ∧ ∀ i, C7101.adjugate i i ≠ 0) := by
  intro h
  have := certificate7101
  rw [h.1] at this
  norm_num at this
def C7102 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7102 : C7102.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7102 : ¬ (C7102.det = 0 ∧ ∀ i, C7102.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7102
def C7103 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7103 : C7103.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7103 : ¬ (C7103.det = 0 ∧ ∀ i, C7103.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate7103
end Nut8.NewCertificates0221
