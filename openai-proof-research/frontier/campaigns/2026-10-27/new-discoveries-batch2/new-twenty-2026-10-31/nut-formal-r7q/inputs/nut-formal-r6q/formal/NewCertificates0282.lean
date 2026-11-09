import VerifiedDet
namespace Nut8.NewCertificates0282
def C9024 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9024 : C9024.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9024 : ¬ (C9024.det = 0 ∧ ∀ i, C9024.adjugate i i ≠ 0) := by
  intro h
  have := certificate9024
  rw [h.1] at this
  norm_num at this
def C9025 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9025 : C9025.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9025 : ¬ (C9025.det = 0 ∧ ∀ i, C9025.adjugate i i ≠ 0) := by
  intro h
  have := certificate9025
  rw [h.1] at this
  norm_num at this
def C9026 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9026 : C9026.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9026 : ¬ (C9026.det = 0 ∧ ∀ i, C9026.adjugate i i ≠ 0) := by
  intro h
  have := certificate9026
  rw [h.1] at this
  norm_num at this
def C9027 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9027 : C9027.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9027 : ¬ (C9027.det = 0 ∧ ∀ i, C9027.adjugate i i ≠ 0) := by
  intro h
  have := certificate9027
  rw [h.1] at this
  norm_num at this
def C9028 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9028 : C9028.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9028 : ¬ (C9028.det = 0 ∧ ∀ i, C9028.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9028
def C9029 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9029 : C9029.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9029 : ¬ (C9029.det = 0 ∧ ∀ i, C9029.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9029
def C9030 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9030 : C9030.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9030 : ¬ (C9030.det = 0 ∧ ∀ i, C9030.adjugate i i ≠ 0) := by
  intro h
  have := certificate9030
  rw [h.1] at this
  norm_num at this
def C9031 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9031 : C9031.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9031 : ¬ (C9031.det = 0 ∧ ∀ i, C9031.adjugate i i ≠ 0) := by
  intro h
  have := certificate9031
  rw [h.1] at this
  norm_num at this
def C9032 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9032 : C9032.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9032 : ¬ (C9032.det = 0 ∧ ∀ i, C9032.adjugate i i ≠ 0) := by
  intro h
  have := certificate9032
  rw [h.1] at this
  norm_num at this
def C9033 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9033 : C9033.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9033 : ¬ (C9033.det = 0 ∧ ∀ i, C9033.adjugate i i ≠ 0) := by
  intro h
  have := certificate9033
  rw [h.1] at this
  norm_num at this
def C9034 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9034 : C9034.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9034 : ¬ (C9034.det = 0 ∧ ∀ i, C9034.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9034
def C9035 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9035 : C9035.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9035 : ¬ (C9035.det = 0 ∧ ∀ i, C9035.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9035
def C9036 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9036 : C9036.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9036 : ¬ (C9036.det = 0 ∧ ∀ i, C9036.adjugate i i ≠ 0) := by
  intro h
  have := certificate9036
  rw [h.1] at this
  norm_num at this
def C9037 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9037 : C9037.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9037 : ¬ (C9037.det = 0 ∧ ∀ i, C9037.adjugate i i ≠ 0) := by
  intro h
  have := certificate9037
  rw [h.1] at this
  norm_num at this
def C9038 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9038 : C9038.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9038 : ¬ (C9038.det = 0 ∧ ∀ i, C9038.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9038
def C9039 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9039 : C9039.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9039 : ¬ (C9039.det = 0 ∧ ∀ i, C9039.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9039
def C9040 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9040 : C9040.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9040 : ¬ (C9040.det = 0 ∧ ∀ i, C9040.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9040
def C9041 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9041 : C9041.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9041 : ¬ (C9041.det = 0 ∧ ∀ i, C9041.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9041
def C9042 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9042 : C9042.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9042 : ¬ (C9042.det = 0 ∧ ∀ i, C9042.adjugate i i ≠ 0) := by
  intro h
  have := certificate9042
  rw [h.1] at this
  norm_num at this
def C9043 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9043 : C9043.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9043 : ¬ (C9043.det = 0 ∧ ∀ i, C9043.adjugate i i ≠ 0) := by
  intro h
  have := certificate9043
  rw [h.1] at this
  norm_num at this
def C9044 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9044 : C9044.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9044 : ¬ (C9044.det = 0 ∧ ∀ i, C9044.adjugate i i ≠ 0) := by
  intro h
  have := certificate9044
  rw [h.1] at this
  norm_num at this
def C9045 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9045 : C9045.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9045 : ¬ (C9045.det = 0 ∧ ∀ i, C9045.adjugate i i ≠ 0) := by
  intro h
  have := certificate9045
  rw [h.1] at this
  norm_num at this
def C9046 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9046 : C9046.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9046 : ¬ (C9046.det = 0 ∧ ∀ i, C9046.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9046
def C9047 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9047 : C9047.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9047 : ¬ (C9047.det = 0 ∧ ∀ i, C9047.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate9047
def C9048 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9048 : C9048.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9048 : ¬ (C9048.det = 0 ∧ ∀ i, C9048.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9048
def C9049 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate9049 : C9049.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9049 : ¬ (C9049.det = 0 ∧ ∀ i, C9049.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9049
def C9050 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9050 : C9050.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9050 : ¬ (C9050.det = 0 ∧ ∀ i, C9050.adjugate i i ≠ 0) := by
  intro h
  have := certificate9050
  rw [h.1] at this
  norm_num at this
def C9051 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate9051 : C9051.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9051 : ¬ (C9051.det = 0 ∧ ∀ i, C9051.adjugate i i ≠ 0) := by
  intro h
  have := certificate9051
  rw [h.1] at this
  norm_num at this
def C9052 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9052 : C9052.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9052 : ¬ (C9052.det = 0 ∧ ∀ i, C9052.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9052
def C9053 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate9053 : C9053.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction9053 : ¬ (C9053.det = 0 ∧ ∀ i, C9053.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate9053
def C9054 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9054 : C9054.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9054 : ¬ (C9054.det = 0 ∧ ∀ i, C9054.adjugate i i ≠ 0) := by
  intro h
  have := certificate9054
  rw [h.1] at this
  norm_num at this
def C9055 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate9055 : C9055.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9055 : ¬ (C9055.det = 0 ∧ ∀ i, C9055.adjugate i i ≠ 0) := by
  intro h
  have := certificate9055
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0282
