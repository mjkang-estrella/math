import VerifiedDet
namespace Nut8.NewCertificates0247
def C7904 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7904 : C7904.det = (-53 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7904 : ¬ (C7904.det = 0 ∧ ∀ i, C7904.adjugate i i ≠ 0) := by
  intro h
  have := certificate7904
  rw [h.1] at this
  norm_num at this
def C7905 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7905 : C7905.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7905 : ¬ (C7905.det = 0 ∧ ∀ i, C7905.adjugate i i ≠ 0) := by
  intro h
  have := certificate7905
  rw [h.1] at this
  norm_num at this
def C7906 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7906 : C7906.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7906 : ¬ (C7906.det = 0 ∧ ∀ i, C7906.adjugate i i ≠ 0) := by
  intro h
  have := certificate7906
  rw [h.1] at this
  norm_num at this
def C7907 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7907 : C7907.det = (-53 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7907 : ¬ (C7907.det = 0 ∧ ∀ i, C7907.adjugate i i ≠ 0) := by
  intro h
  have := certificate7907
  rw [h.1] at this
  norm_num at this
def C7908 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7908 : C7908.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7908 : ¬ (C7908.det = 0 ∧ ∀ i, C7908.adjugate i i ≠ 0) := by
  intro h
  have := certificate7908
  rw [h.1] at this
  norm_num at this
def C7909 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7909 : C7909.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7909 : ¬ (C7909.det = 0 ∧ ∀ i, C7909.adjugate i i ≠ 0) := by
  intro h
  have := certificate7909
  rw [h.1] at this
  norm_num at this
def C7910 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7910 : C7910.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7910 : ¬ (C7910.det = 0 ∧ ∀ i, C7910.adjugate i i ≠ 0) := by
  intro h
  have := certificate7910
  rw [h.1] at this
  norm_num at this
def C7911 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7911 : C7911.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7911 : ¬ (C7911.det = 0 ∧ ∀ i, C7911.adjugate i i ≠ 0) := by
  intro h
  have := certificate7911
  rw [h.1] at this
  norm_num at this
def C7912 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7912 : C7912.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7912 : ¬ (C7912.det = 0 ∧ ∀ i, C7912.adjugate i i ≠ 0) := by
  intro h
  have := certificate7912
  rw [h.1] at this
  norm_num at this
def C7913 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7913 : C7913.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7913 : ¬ (C7913.det = 0 ∧ ∀ i, C7913.adjugate i i ≠ 0) := by
  intro h
  have := certificate7913
  rw [h.1] at this
  norm_num at this
def C7914 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7914 : C7914.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7914 : ¬ (C7914.det = 0 ∧ ∀ i, C7914.adjugate i i ≠ 0) := by
  intro h
  have := certificate7914
  rw [h.1] at this
  norm_num at this
def C7915 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7915 : C7915.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7915 : ¬ (C7915.det = 0 ∧ ∀ i, C7915.adjugate i i ≠ 0) := by
  intro h
  have := certificate7915
  rw [h.1] at this
  norm_num at this
def C7916 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7916 : C7916.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7916 : ¬ (C7916.det = 0 ∧ ∀ i, C7916.adjugate i i ≠ 0) := by
  intro h
  have := certificate7916
  rw [h.1] at this
  norm_num at this
def C7917 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7917 : C7917.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7917 : ¬ (C7917.det = 0 ∧ ∀ i, C7917.adjugate i i ≠ 0) := by
  intro h
  have := certificate7917
  rw [h.1] at this
  norm_num at this
def C7918 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7918 : C7918.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7918 : ¬ (C7918.det = 0 ∧ ∀ i, C7918.adjugate i i ≠ 0) := by
  intro h
  have := certificate7918
  rw [h.1] at this
  norm_num at this
def C7919 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7919 : C7919.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7919 : ¬ (C7919.det = 0 ∧ ∀ i, C7919.adjugate i i ≠ 0) := by
  intro h
  have := certificate7919
  rw [h.1] at this
  norm_num at this
def C7920 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7920 : C7920.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7920 : ¬ (C7920.det = 0 ∧ ∀ i, C7920.adjugate i i ≠ 0) := by
  intro h
  have := certificate7920
  rw [h.1] at this
  norm_num at this
def C7921 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7921 : C7921.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7921 : ¬ (C7921.det = 0 ∧ ∀ i, C7921.adjugate i i ≠ 0) := by
  intro h
  have := certificate7921
  rw [h.1] at this
  norm_num at this
def C7922 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7922 : C7922.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7922 : ¬ (C7922.det = 0 ∧ ∀ i, C7922.adjugate i i ≠ 0) := by
  intro h
  have := certificate7922
  rw [h.1] at this
  norm_num at this
def C7923 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7923 : C7923.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7923 : ¬ (C7923.det = 0 ∧ ∀ i, C7923.adjugate i i ≠ 0) := by
  intro h
  have := certificate7923
  rw [h.1] at this
  norm_num at this
def C7924 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7924 : C7924.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7924 : ¬ (C7924.det = 0 ∧ ∀ i, C7924.adjugate i i ≠ 0) := by
  intro h
  have := certificate7924
  rw [h.1] at this
  norm_num at this
def C7925 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7925 : C7925.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7925 : ¬ (C7925.det = 0 ∧ ∀ i, C7925.adjugate i i ≠ 0) := by
  intro h
  have := certificate7925
  rw [h.1] at this
  norm_num at this
def C7926 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7926 : C7926.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7926 : ¬ (C7926.det = 0 ∧ ∀ i, C7926.adjugate i i ≠ 0) := by
  intro h
  have := certificate7926
  rw [h.1] at this
  norm_num at this
def C7927 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7927 : C7927.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7927 : ¬ (C7927.det = 0 ∧ ∀ i, C7927.adjugate i i ≠ 0) := by
  intro h
  have := certificate7927
  rw [h.1] at this
  norm_num at this
def C7928 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7928 : C7928.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7928 : ¬ (C7928.det = 0 ∧ ∀ i, C7928.adjugate i i ≠ 0) := by
  intro h
  have := certificate7928
  rw [h.1] at this
  norm_num at this
def C7929 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7929 : C7929.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7929 : ¬ (C7929.det = 0 ∧ ∀ i, C7929.adjugate i i ≠ 0) := by
  intro h
  have := certificate7929
  rw [h.1] at this
  norm_num at this
def C7930 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7930 : C7930.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7930 : ¬ (C7930.det = 0 ∧ ∀ i, C7930.adjugate i i ≠ 0) := by
  intro h
  have := certificate7930
  rw [h.1] at this
  norm_num at this
def C7931 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7931 : C7931.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7931 : ¬ (C7931.det = 0 ∧ ∀ i, C7931.adjugate i i ≠ 0) := by
  intro h
  have := certificate7931
  rw [h.1] at this
  norm_num at this
def C7932 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7932 : C7932.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7932 : ¬ (C7932.det = 0 ∧ ∀ i, C7932.adjugate i i ≠ 0) := by
  intro h
  have := certificate7932
  rw [h.1] at this
  norm_num at this
def C7933 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7933 : C7933.det = (70 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7933 : ¬ (C7933.det = 0 ∧ ∀ i, C7933.adjugate i i ≠ 0) := by
  intro h
  have := certificate7933
  rw [h.1] at this
  norm_num at this
def C7934 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7934 : C7934.det = (30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7934 : ¬ (C7934.det = 0 ∧ ∀ i, C7934.adjugate i i ≠ 0) := by
  intro h
  have := certificate7934
  rw [h.1] at this
  norm_num at this
def C7935 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7935 : C7935.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7935 : ¬ (C7935.det = 0 ∧ ∀ i, C7935.adjugate i i ≠ 0) := by
  intro h
  have := certificate7935
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0247
