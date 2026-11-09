import VerifiedDet
namespace Nut8.NewCertificates0122
def C3904 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate3904 : C3904.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3904 : ¬ (C3904.det = 0 ∧ ∀ i, C3904.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3904
def C3905 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate3905 : C3905.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3905 : ¬ (C3905.det = 0 ∧ ∀ i, C3905.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3905
def C3906 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate3906 : C3906.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3906 : ¬ (C3906.det = 0 ∧ ∀ i, C3906.adjugate i i ≠ 0) := by
  intro h
  have := certificate3906
  rw [h.1] at this
  norm_num at this
def C3907 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate3907 : C3907.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3907 : ¬ (C3907.det = 0 ∧ ∀ i, C3907.adjugate i i ≠ 0) := by
  intro h
  have := certificate3907
  rw [h.1] at this
  norm_num at this
def C3908 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate3908 : C3908.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3908 : ¬ (C3908.det = 0 ∧ ∀ i, C3908.adjugate i i ≠ 0) := by
  intro h
  have := certificate3908
  rw [h.1] at this
  norm_num at this
def C3909 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate3909 : C3909.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3909 : ¬ (C3909.det = 0 ∧ ∀ i, C3909.adjugate i i ≠ 0) := by
  intro h
  have := certificate3909
  rw [h.1] at this
  norm_num at this
def C3910 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate3910 : C3910.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3910 : ¬ (C3910.det = 0 ∧ ∀ i, C3910.adjugate i i ≠ 0) := by
  intro h
  have := certificate3910
  rw [h.1] at this
  norm_num at this
def C3911 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate3911 : C3911.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3911 : ¬ (C3911.det = 0 ∧ ∀ i, C3911.adjugate i i ≠ 0) := by
  intro h
  have := certificate3911
  rw [h.1] at this
  norm_num at this
def C3912 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate3912 : C3912.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3912 : ¬ (C3912.det = 0 ∧ ∀ i, C3912.adjugate i i ≠ 0) := by
  intro h
  have := certificate3912
  rw [h.1] at this
  norm_num at this
def C3913 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate3913 : C3913.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3913 : ¬ (C3913.det = 0 ∧ ∀ i, C3913.adjugate i i ≠ 0) := by
  intro h
  have := certificate3913
  rw [h.1] at this
  norm_num at this
def C3914 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate3914 : C3914.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3914 : ¬ (C3914.det = 0 ∧ ∀ i, C3914.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3914
def C3915 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate3915 : C3915.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3915 : ¬ (C3915.det = 0 ∧ ∀ i, C3915.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3915
def C3916 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate3916 : C3916.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3916 : ¬ (C3916.det = 0 ∧ ∀ i, C3916.adjugate i i ≠ 0) := by
  intro h
  have := certificate3916
  rw [h.1] at this
  norm_num at this
def C3917 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate3917 : C3917.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3917 : ¬ (C3917.det = 0 ∧ ∀ i, C3917.adjugate i i ≠ 0) := by
  intro h
  have := certificate3917
  rw [h.1] at this
  norm_num at this
def C3918 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate3918 : C3918.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3918 : ¬ (C3918.det = 0 ∧ ∀ i, C3918.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3918
def C3919 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate3919 : C3919.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3919 : ¬ (C3919.det = 0 ∧ ∀ i, C3919.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3919
def C3920 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate3920 : C3920.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3920 : ¬ (C3920.det = 0 ∧ ∀ i, C3920.adjugate i i ≠ 0) := by
  intro h
  have := certificate3920
  rw [h.1] at this
  norm_num at this
def C3921 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate3921 : C3921.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3921 : ¬ (C3921.det = 0 ∧ ∀ i, C3921.adjugate i i ≠ 0) := by
  intro h
  have := certificate3921
  rw [h.1] at this
  norm_num at this
def C3922 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate3922 : C3922.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3922 : ¬ (C3922.det = 0 ∧ ∀ i, C3922.adjugate i i ≠ 0) := by
  intro h
  have := certificate3922
  rw [h.1] at this
  norm_num at this
def C3923 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate3923 : C3923.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3923 : ¬ (C3923.det = 0 ∧ ∀ i, C3923.adjugate i i ≠ 0) := by
  intro h
  have := certificate3923
  rw [h.1] at this
  norm_num at this
def C3924 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate3924 : C3924.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3924 : ¬ (C3924.det = 0 ∧ ∀ i, C3924.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3924
def C3925 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate3925 : C3925.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3925 : ¬ (C3925.det = 0 ∧ ∀ i, C3925.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3925
def C3926 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate3926 : C3926.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3926 : ¬ (C3926.det = 0 ∧ ∀ i, C3926.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3926
def C3927 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate3927 : C3927.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3927 : ¬ (C3927.det = 0 ∧ ∀ i, C3927.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3927
def C3928 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate3928 : C3928.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3928 : ¬ (C3928.det = 0 ∧ ∀ i, C3928.adjugate i i ≠ 0) := by
  intro h
  have := certificate3928
  rw [h.1] at this
  norm_num at this
def C3929 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate3929 : C3929.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3929 : ¬ (C3929.det = 0 ∧ ∀ i, C3929.adjugate i i ≠ 0) := by
  intro h
  have := certificate3929
  rw [h.1] at this
  norm_num at this
def C3930 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate3930 : C3930.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3930 : ¬ (C3930.det = 0 ∧ ∀ i, C3930.adjugate i i ≠ 0) := by
  intro h
  have := certificate3930
  rw [h.1] at this
  norm_num at this
def C3931 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0]
theorem certificate3931 : C3931.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3931 : ¬ (C3931.det = 0 ∧ ∀ i, C3931.adjugate i i ≠ 0) := by
  intro h
  have := certificate3931
  rw [h.1] at this
  norm_num at this
def C3932 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate3932 : C3932.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3932 : ¬ (C3932.det = 0 ∧ ∀ i, C3932.adjugate i i ≠ 0) := by
  intro h
  have := certificate3932
  rw [h.1] at this
  norm_num at this
def C3933 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, -1, 0]
theorem certificate3933 : C3933.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3933 : ¬ (C3933.det = 0 ∧ ∀ i, C3933.adjugate i i ≠ 0) := by
  intro h
  have := certificate3933
  rw [h.1] at this
  norm_num at this
def C3934 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate3934 : C3934.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3934 : ¬ (C3934.det = 0 ∧ ∀ i, C3934.adjugate i i ≠ 0) := by
  intro h
  have := certificate3934
  rw [h.1] at this
  norm_num at this
def C3935 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0]
theorem certificate3935 : C3935.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3935 : ¬ (C3935.det = 0 ∧ ∀ i, C3935.adjugate i i ≠ 0) := by
  intro h
  have := certificate3935
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0122
