import VerifiedDet
namespace Nut8.NewCertificates0215
def C6880 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6880 : C6880.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6880 : ¬ (C6880.det = 0 ∧ ∀ i, C6880.adjugate i i ≠ 0) := by
  intro h
  have := certificate6880
  rw [h.1] at this
  norm_num at this
def C6881 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6881 : C6881.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6881 : ¬ (C6881.det = 0 ∧ ∀ i, C6881.adjugate i i ≠ 0) := by
  intro h
  have := certificate6881
  rw [h.1] at this
  norm_num at this
def C6882 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6882 : C6882.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6882 : ¬ (C6882.det = 0 ∧ ∀ i, C6882.adjugate i i ≠ 0) := by
  intro h
  have := certificate6882
  rw [h.1] at this
  norm_num at this
def C6883 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6883 : C6883.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6883 : ¬ (C6883.det = 0 ∧ ∀ i, C6883.adjugate i i ≠ 0) := by
  intro h
  have := certificate6883
  rw [h.1] at this
  norm_num at this
def C6884 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6884 : C6884.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6884 : ¬ (C6884.det = 0 ∧ ∀ i, C6884.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6884
def C6885 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6885 : C6885.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6885 : ¬ (C6885.det = 0 ∧ ∀ i, C6885.adjugate i i ≠ 0) := by
  intro h
  have := certificate6885
  rw [h.1] at this
  norm_num at this
def C6886 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6886 : C6886.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6886 : ¬ (C6886.det = 0 ∧ ∀ i, C6886.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6886
def C6887 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6887 : C6887.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6887 : ¬ (C6887.det = 0 ∧ ∀ i, C6887.adjugate i i ≠ 0) := by
  intro h
  have := certificate6887
  rw [h.1] at this
  norm_num at this
def C6888 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6888 : C6888.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6888 : ¬ (C6888.det = 0 ∧ ∀ i, C6888.adjugate i i ≠ 0) := by
  intro h
  have := certificate6888
  rw [h.1] at this
  norm_num at this
def C6889 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6889 : C6889.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6889 : ¬ (C6889.det = 0 ∧ ∀ i, C6889.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6889
def C6890 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6890 : C6890.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6890 : ¬ (C6890.det = 0 ∧ ∀ i, C6890.adjugate i i ≠ 0) := by
  intro h
  have := certificate6890
  rw [h.1] at this
  norm_num at this
def C6891 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6891 : C6891.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6891 : ¬ (C6891.det = 0 ∧ ∀ i, C6891.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6891
def C6892 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6892 : C6892.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6892 : ¬ (C6892.det = 0 ∧ ∀ i, C6892.adjugate i i ≠ 0) := by
  intro h
  have := certificate6892
  rw [h.1] at this
  norm_num at this
def C6893 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6893 : C6893.det = (68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6893 : ¬ (C6893.det = 0 ∧ ∀ i, C6893.adjugate i i ≠ 0) := by
  intro h
  have := certificate6893
  rw [h.1] at this
  norm_num at this
def C6894 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6894 : C6894.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6894 : ¬ (C6894.det = 0 ∧ ∀ i, C6894.adjugate i i ≠ 0) := by
  intro h
  have := certificate6894
  rw [h.1] at this
  norm_num at this
def C6895 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6895 : C6895.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6895 : ¬ (C6895.det = 0 ∧ ∀ i, C6895.adjugate i i ≠ 0) := by
  intro h
  have := certificate6895
  rw [h.1] at this
  norm_num at this
def C6896 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6896 : C6896.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6896 : ¬ (C6896.det = 0 ∧ ∀ i, C6896.adjugate i i ≠ 0) := by
  intro h
  have := certificate6896
  rw [h.1] at this
  norm_num at this
def C6897 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6897 : C6897.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6897 : ¬ (C6897.det = 0 ∧ ∀ i, C6897.adjugate i i ≠ 0) := by
  intro h
  have := certificate6897
  rw [h.1] at this
  norm_num at this
def C6898 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6898 : C6898.det = (68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6898 : ¬ (C6898.det = 0 ∧ ∀ i, C6898.adjugate i i ≠ 0) := by
  intro h
  have := certificate6898
  rw [h.1] at this
  norm_num at this
def C6899 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6899 : C6899.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6899 : ¬ (C6899.det = 0 ∧ ∀ i, C6899.adjugate i i ≠ 0) := by
  intro h
  have := certificate6899
  rw [h.1] at this
  norm_num at this
def C6900 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6900 : C6900.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6900 : ¬ (C6900.det = 0 ∧ ∀ i, C6900.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6900
def C6901 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6901 : C6901.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6901 : ¬ (C6901.det = 0 ∧ ∀ i, C6901.adjugate i i ≠ 0) := by
  intro h
  have := certificate6901
  rw [h.1] at this
  norm_num at this
def C6902 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6902 : C6902.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6902 : ¬ (C6902.det = 0 ∧ ∀ i, C6902.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6902
def C6903 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6903 : C6903.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6903 : ¬ (C6903.det = 0 ∧ ∀ i, C6903.adjugate i i ≠ 0) := by
  intro h
  have := certificate6903
  rw [h.1] at this
  norm_num at this
def C6904 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6904 : C6904.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6904 : ¬ (C6904.det = 0 ∧ ∀ i, C6904.adjugate i i ≠ 0) := by
  intro h
  have := certificate6904
  rw [h.1] at this
  norm_num at this
def C6905 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6905 : C6905.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6905 : ¬ (C6905.det = 0 ∧ ∀ i, C6905.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6905
def C6906 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6906 : C6906.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6906 : ¬ (C6906.det = 0 ∧ ∀ i, C6906.adjugate i i ≠ 0) := by
  intro h
  have := certificate6906
  rw [h.1] at this
  norm_num at this
def C6907 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6907 : C6907.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6907 : ¬ (C6907.det = 0 ∧ ∀ i, C6907.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6907
def C6908 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6908 : C6908.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6908 : ¬ (C6908.det = 0 ∧ ∀ i, C6908.adjugate i i ≠ 0) := by
  intro h
  have := certificate6908
  rw [h.1] at this
  norm_num at this
def C6909 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6909 : C6909.det = (68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6909 : ¬ (C6909.det = 0 ∧ ∀ i, C6909.adjugate i i ≠ 0) := by
  intro h
  have := certificate6909
  rw [h.1] at this
  norm_num at this
def C6910 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6910 : C6910.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6910 : ¬ (C6910.det = 0 ∧ ∀ i, C6910.adjugate i i ≠ 0) := by
  intro h
  have := certificate6910
  rw [h.1] at this
  norm_num at this
def C6911 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6911 : C6911.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6911 : ¬ (C6911.det = 0 ∧ ∀ i, C6911.adjugate i i ≠ 0) := by
  intro h
  have := certificate6911
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0215
