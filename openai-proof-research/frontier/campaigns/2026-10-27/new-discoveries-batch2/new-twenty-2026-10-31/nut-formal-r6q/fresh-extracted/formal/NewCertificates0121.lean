import VerifiedDet
namespace Nut8.NewCertificates0121
def C3872 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3872 : C3872.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3872 : ¬ (C3872.det = 0 ∧ ∀ i, C3872.adjugate i i ≠ 0) := by
  intro h
  have := certificate3872
  rw [h.1] at this
  norm_num at this
def C3873 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3873 : C3873.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3873 : ¬ (C3873.det = 0 ∧ ∀ i, C3873.adjugate i i ≠ 0) := by
  intro h
  have := certificate3873
  rw [h.1] at this
  norm_num at this
def C3874 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3874 : C3874.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3874 : ¬ (C3874.det = 0 ∧ ∀ i, C3874.adjugate i i ≠ 0) := by
  intro h
  have := certificate3874
  rw [h.1] at this
  norm_num at this
def C3875 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3875 : C3875.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3875 : ¬ (C3875.det = 0 ∧ ∀ i, C3875.adjugate i i ≠ 0) := by
  intro h
  have := certificate3875
  rw [h.1] at this
  norm_num at this
def C3876 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3876 : C3876.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3876 : ¬ (C3876.det = 0 ∧ ∀ i, C3876.adjugate i i ≠ 0) := by
  intro h
  have := certificate3876
  rw [h.1] at this
  norm_num at this
def C3877 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3877 : C3877.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3877 : ¬ (C3877.det = 0 ∧ ∀ i, C3877.adjugate i i ≠ 0) := by
  intro h
  have := certificate3877
  rw [h.1] at this
  norm_num at this
def C3878 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3878 : C3878.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3878 : ¬ (C3878.det = 0 ∧ ∀ i, C3878.adjugate i i ≠ 0) := by
  intro h
  have := certificate3878
  rw [h.1] at this
  norm_num at this
def C3879 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3879 : C3879.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3879 : ¬ (C3879.det = 0 ∧ ∀ i, C3879.adjugate i i ≠ 0) := by
  intro h
  have := certificate3879
  rw [h.1] at this
  norm_num at this
def C3880 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3880 : C3880.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3880 : ¬ (C3880.det = 0 ∧ ∀ i, C3880.adjugate i i ≠ 0) := by
  intro h
  have := certificate3880
  rw [h.1] at this
  norm_num at this
def C3881 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3881 : C3881.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3881 : ¬ (C3881.det = 0 ∧ ∀ i, C3881.adjugate i i ≠ 0) := by
  intro h
  have := certificate3881
  rw [h.1] at this
  norm_num at this
def C3882 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3882 : C3882.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3882 : ¬ (C3882.det = 0 ∧ ∀ i, C3882.adjugate i i ≠ 0) := by
  intro h
  have := certificate3882
  rw [h.1] at this
  norm_num at this
def C3883 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3883 : C3883.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3883 : ¬ (C3883.det = 0 ∧ ∀ i, C3883.adjugate i i ≠ 0) := by
  intro h
  have := certificate3883
  rw [h.1] at this
  norm_num at this
def C3884 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3884 : C3884.det = (-27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3884 : ¬ (C3884.det = 0 ∧ ∀ i, C3884.adjugate i i ≠ 0) := by
  intro h
  have := certificate3884
  rw [h.1] at this
  norm_num at this
def C3885 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3885 : C3885.det = (45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3885 : ¬ (C3885.det = 0 ∧ ∀ i, C3885.adjugate i i ≠ 0) := by
  intro h
  have := certificate3885
  rw [h.1] at this
  norm_num at this
def C3886 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3886 : C3886.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3886 : ¬ (C3886.det = 0 ∧ ∀ i, C3886.adjugate i i ≠ 0) := by
  intro h
  have := certificate3886
  rw [h.1] at this
  norm_num at this
def C3887 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3887 : C3887.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3887 : ¬ (C3887.det = 0 ∧ ∀ i, C3887.adjugate i i ≠ 0) := by
  intro h
  have := certificate3887
  rw [h.1] at this
  norm_num at this
def C3888 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3888 : C3888.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3888 : ¬ (C3888.det = 0 ∧ ∀ i, C3888.adjugate i i ≠ 0) := by
  intro h
  have := certificate3888
  rw [h.1] at this
  norm_num at this
def C3889 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3889 : C3889.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3889 : ¬ (C3889.det = 0 ∧ ∀ i, C3889.adjugate i i ≠ 0) := by
  intro h
  have := certificate3889
  rw [h.1] at this
  norm_num at this
def C3890 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3890 : C3890.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3890 : ¬ (C3890.det = 0 ∧ ∀ i, C3890.adjugate i i ≠ 0) := by
  intro h
  have := certificate3890
  rw [h.1] at this
  norm_num at this
def C3891 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3891 : C3891.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3891 : ¬ (C3891.det = 0 ∧ ∀ i, C3891.adjugate i i ≠ 0) := by
  intro h
  have := certificate3891
  rw [h.1] at this
  norm_num at this
def C3892 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3892 : C3892.det = (45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3892 : ¬ (C3892.det = 0 ∧ ∀ i, C3892.adjugate i i ≠ 0) := by
  intro h
  have := certificate3892
  rw [h.1] at this
  norm_num at this
def C3893 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3893 : C3893.det = (-27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3893 : ¬ (C3893.det = 0 ∧ ∀ i, C3893.adjugate i i ≠ 0) := by
  intro h
  have := certificate3893
  rw [h.1] at this
  norm_num at this
def C3894 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate3894 : C3894.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3894 : ¬ (C3894.det = 0 ∧ ∀ i, C3894.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3894
def C3895 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate3895 : C3895.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3895 : ¬ (C3895.det = 0 ∧ ∀ i, C3895.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3895
def C3896 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate3896 : C3896.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3896 : ¬ (C3896.det = 0 ∧ ∀ i, C3896.adjugate i i ≠ 0) := by
  intro h
  have := certificate3896
  rw [h.1] at this
  norm_num at this
def C3897 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate3897 : C3897.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3897 : ¬ (C3897.det = 0 ∧ ∀ i, C3897.adjugate i i ≠ 0) := by
  intro h
  have := certificate3897
  rw [h.1] at this
  norm_num at this
def C3898 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate3898 : C3898.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3898 : ¬ (C3898.det = 0 ∧ ∀ i, C3898.adjugate i i ≠ 0) := by
  intro h
  have := certificate3898
  rw [h.1] at this
  norm_num at this
def C3899 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate3899 : C3899.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3899 : ¬ (C3899.det = 0 ∧ ∀ i, C3899.adjugate i i ≠ 0) := by
  intro h
  have := certificate3899
  rw [h.1] at this
  norm_num at this
def C3900 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate3900 : C3900.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3900 : ¬ (C3900.det = 0 ∧ ∀ i, C3900.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3900
def C3901 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate3901 : C3901.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3901 : ¬ (C3901.det = 0 ∧ ∀ i, C3901.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3901
def C3902 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate3902 : C3902.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3902 : ¬ (C3902.det = 0 ∧ ∀ i, C3902.adjugate i i ≠ 0) := by
  intro h
  have := certificate3902
  rw [h.1] at this
  norm_num at this
def C3903 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate3903 : C3903.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3903 : ¬ (C3903.det = 0 ∧ ∀ i, C3903.adjugate i i ≠ 0) := by
  intro h
  have := certificate3903
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0121
