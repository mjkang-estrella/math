import VerifiedDet
namespace Nut8.NewCertificates0220
def C7040 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7040 : C7040.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7040 : ¬ (C7040.det = 0 ∧ ∀ i, C7040.adjugate i i ≠ 0) := by
  intro h
  have := certificate7040
  rw [h.1] at this
  norm_num at this
def C7041 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7041 : C7041.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7041 : ¬ (C7041.det = 0 ∧ ∀ i, C7041.adjugate i i ≠ 0) := by
  intro h
  have := certificate7041
  rw [h.1] at this
  norm_num at this
def C7042 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7042 : C7042.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7042 : ¬ (C7042.det = 0 ∧ ∀ i, C7042.adjugate i i ≠ 0) := by
  intro h
  have := certificate7042
  rw [h.1] at this
  norm_num at this
def C7043 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7043 : C7043.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7043 : ¬ (C7043.det = 0 ∧ ∀ i, C7043.adjugate i i ≠ 0) := by
  intro h
  have := certificate7043
  rw [h.1] at this
  norm_num at this
def C7044 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7044 : C7044.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7044 : ¬ (C7044.det = 0 ∧ ∀ i, C7044.adjugate i i ≠ 0) := by
  intro h
  have := certificate7044
  rw [h.1] at this
  norm_num at this
def C7045 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7045 : C7045.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7045 : ¬ (C7045.det = 0 ∧ ∀ i, C7045.adjugate i i ≠ 0) := by
  intro h
  have := certificate7045
  rw [h.1] at this
  norm_num at this
def C7046 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7046 : C7046.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7046 : ¬ (C7046.det = 0 ∧ ∀ i, C7046.adjugate i i ≠ 0) := by
  intro h
  have := certificate7046
  rw [h.1] at this
  norm_num at this
def C7047 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7047 : C7047.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7047 : ¬ (C7047.det = 0 ∧ ∀ i, C7047.adjugate i i ≠ 0) := by
  intro h
  have := certificate7047
  rw [h.1] at this
  norm_num at this
def C7048 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7048 : C7048.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7048 : ¬ (C7048.det = 0 ∧ ∀ i, C7048.adjugate i i ≠ 0) := by
  intro h
  have := certificate7048
  rw [h.1] at this
  norm_num at this
def C7049 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7049 : C7049.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7049 : ¬ (C7049.det = 0 ∧ ∀ i, C7049.adjugate i i ≠ 0) := by
  intro h
  have := certificate7049
  rw [h.1] at this
  norm_num at this
def C7050 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7050 : C7050.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7050 : ¬ (C7050.det = 0 ∧ ∀ i, C7050.adjugate i i ≠ 0) := by
  intro h
  have := certificate7050
  rw [h.1] at this
  norm_num at this
def C7051 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7051 : C7051.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7051 : ¬ (C7051.det = 0 ∧ ∀ i, C7051.adjugate i i ≠ 0) := by
  intro h
  have := certificate7051
  rw [h.1] at this
  norm_num at this
def C7052 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7052 : C7052.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7052 : ¬ (C7052.det = 0 ∧ ∀ i, C7052.adjugate i i ≠ 0) := by
  intro h
  have := certificate7052
  rw [h.1] at this
  norm_num at this
def C7053 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7053 : C7053.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7053 : ¬ (C7053.det = 0 ∧ ∀ i, C7053.adjugate i i ≠ 0) := by
  intro h
  have := certificate7053
  rw [h.1] at this
  norm_num at this
def C7054 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7054 : C7054.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7054 : ¬ (C7054.det = 0 ∧ ∀ i, C7054.adjugate i i ≠ 0) := by
  intro h
  have := certificate7054
  rw [h.1] at this
  norm_num at this
def C7055 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7055 : C7055.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7055 : ¬ (C7055.det = 0 ∧ ∀ i, C7055.adjugate i i ≠ 0) := by
  intro h
  have := certificate7055
  rw [h.1] at this
  norm_num at this
def C7056 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7056 : C7056.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7056 : ¬ (C7056.det = 0 ∧ ∀ i, C7056.adjugate i i ≠ 0) := by
  intro h
  have := certificate7056
  rw [h.1] at this
  norm_num at this
def C7057 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7057 : C7057.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7057 : ¬ (C7057.det = 0 ∧ ∀ i, C7057.adjugate i i ≠ 0) := by
  intro h
  have := certificate7057
  rw [h.1] at this
  norm_num at this
def C7058 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7058 : C7058.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7058 : ¬ (C7058.det = 0 ∧ ∀ i, C7058.adjugate i i ≠ 0) := by
  intro h
  have := certificate7058
  rw [h.1] at this
  norm_num at this
def C7059 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7059 : C7059.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7059 : ¬ (C7059.det = 0 ∧ ∀ i, C7059.adjugate i i ≠ 0) := by
  intro h
  have := certificate7059
  rw [h.1] at this
  norm_num at this
def C7060 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7060 : C7060.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7060 : ¬ (C7060.det = 0 ∧ ∀ i, C7060.adjugate i i ≠ 0) := by
  intro h
  have := certificate7060
  rw [h.1] at this
  norm_num at this
def C7061 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7061 : C7061.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7061 : ¬ (C7061.det = 0 ∧ ∀ i, C7061.adjugate i i ≠ 0) := by
  intro h
  have := certificate7061
  rw [h.1] at this
  norm_num at this
def C7062 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7062 : C7062.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7062 : ¬ (C7062.det = 0 ∧ ∀ i, C7062.adjugate i i ≠ 0) := by
  intro h
  have := certificate7062
  rw [h.1] at this
  norm_num at this
def C7063 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7063 : C7063.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7063 : ¬ (C7063.det = 0 ∧ ∀ i, C7063.adjugate i i ≠ 0) := by
  intro h
  have := certificate7063
  rw [h.1] at this
  norm_num at this
def C7064 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7064 : C7064.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7064 : ¬ (C7064.det = 0 ∧ ∀ i, C7064.adjugate i i ≠ 0) := by
  intro h
  have := certificate7064
  rw [h.1] at this
  norm_num at this
def C7065 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7065 : C7065.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7065 : ¬ (C7065.det = 0 ∧ ∀ i, C7065.adjugate i i ≠ 0) := by
  intro h
  have := certificate7065
  rw [h.1] at this
  norm_num at this
def C7066 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7066 : C7066.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7066 : ¬ (C7066.det = 0 ∧ ∀ i, C7066.adjugate i i ≠ 0) := by
  intro h
  have := certificate7066
  rw [h.1] at this
  norm_num at this
def C7067 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7067 : C7067.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7067 : ¬ (C7067.det = 0 ∧ ∀ i, C7067.adjugate i i ≠ 0) := by
  intro h
  have := certificate7067
  rw [h.1] at this
  norm_num at this
def C7068 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7068 : C7068.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7068 : ¬ (C7068.det = 0 ∧ ∀ i, C7068.adjugate i i ≠ 0) := by
  intro h
  have := certificate7068
  rw [h.1] at this
  norm_num at this
def C7069 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7069 : C7069.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7069 : ¬ (C7069.det = 0 ∧ ∀ i, C7069.adjugate i i ≠ 0) := by
  intro h
  have := certificate7069
  rw [h.1] at this
  norm_num at this
def C7070 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7070 : C7070.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7070 : ¬ (C7070.det = 0 ∧ ∀ i, C7070.adjugate i i ≠ 0) := by
  intro h
  have := certificate7070
  rw [h.1] at this
  norm_num at this
def C7071 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7071 : C7071.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7071 : ¬ (C7071.det = 0 ∧ ∀ i, C7071.adjugate i i ≠ 0) := by
  intro h
  have := certificate7071
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0220
