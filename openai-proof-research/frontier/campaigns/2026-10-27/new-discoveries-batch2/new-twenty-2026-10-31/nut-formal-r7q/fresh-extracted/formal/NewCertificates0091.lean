import VerifiedDet
namespace Nut8.NewCertificates0091
def C2912 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2912 : C2912.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2912 : ¬ (C2912.det = 0 ∧ ∀ i, C2912.adjugate i i ≠ 0) := by
  intro h
  have := certificate2912
  rw [h.1] at this
  norm_num at this
def C2913 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2913 : C2913.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2913 : ¬ (C2913.det = 0 ∧ ∀ i, C2913.adjugate i i ≠ 0) := by
  intro h
  have := certificate2913
  rw [h.1] at this
  norm_num at this
def C2914 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2914 : C2914.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2914 : ¬ (C2914.det = 0 ∧ ∀ i, C2914.adjugate i i ≠ 0) := by
  intro h
  have := certificate2914
  rw [h.1] at this
  norm_num at this
def C2915 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2915 : C2915.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2915 : ¬ (C2915.det = 0 ∧ ∀ i, C2915.adjugate i i ≠ 0) := by
  intro h
  have := certificate2915
  rw [h.1] at this
  norm_num at this
def C2916 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2916 : C2916.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2916 : ¬ (C2916.det = 0 ∧ ∀ i, C2916.adjugate i i ≠ 0) := by
  intro h
  have := certificate2916
  rw [h.1] at this
  norm_num at this
def C2917 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2917 : C2917.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2917 : ¬ (C2917.det = 0 ∧ ∀ i, C2917.adjugate i i ≠ 0) := by
  intro h
  have := certificate2917
  rw [h.1] at this
  norm_num at this
def C2918 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2918 : C2918.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2918 : ¬ (C2918.det = 0 ∧ ∀ i, C2918.adjugate i i ≠ 0) := by
  intro h
  have := certificate2918
  rw [h.1] at this
  norm_num at this
def C2919 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2919 : C2919.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2919 : ¬ (C2919.det = 0 ∧ ∀ i, C2919.adjugate i i ≠ 0) := by
  intro h
  have := certificate2919
  rw [h.1] at this
  norm_num at this
def C2920 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2920 : C2920.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2920 : ¬ (C2920.det = 0 ∧ ∀ i, C2920.adjugate i i ≠ 0) := by
  intro h
  have := certificate2920
  rw [h.1] at this
  norm_num at this
def C2921 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2921 : C2921.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2921 : ¬ (C2921.det = 0 ∧ ∀ i, C2921.adjugate i i ≠ 0) := by
  intro h
  have := certificate2921
  rw [h.1] at this
  norm_num at this
def C2922 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2922 : C2922.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2922 : ¬ (C2922.det = 0 ∧ ∀ i, C2922.adjugate i i ≠ 0) := by
  intro h
  have := certificate2922
  rw [h.1] at this
  norm_num at this
def C2923 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2923 : C2923.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2923 : ¬ (C2923.det = 0 ∧ ∀ i, C2923.adjugate i i ≠ 0) := by
  intro h
  have := certificate2923
  rw [h.1] at this
  norm_num at this
def C2924 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2924 : C2924.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2924 : ¬ (C2924.det = 0 ∧ ∀ i, C2924.adjugate i i ≠ 0) := by
  intro h
  have := certificate2924
  rw [h.1] at this
  norm_num at this
def C2925 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2925 : C2925.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2925 : ¬ (C2925.det = 0 ∧ ∀ i, C2925.adjugate i i ≠ 0) := by
  intro h
  have := certificate2925
  rw [h.1] at this
  norm_num at this
def C2926 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2926 : C2926.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2926 : ¬ (C2926.det = 0 ∧ ∀ i, C2926.adjugate i i ≠ 0) := by
  intro h
  have := certificate2926
  rw [h.1] at this
  norm_num at this
def C2927 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2927 : C2927.det = (37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2927 : ¬ (C2927.det = 0 ∧ ∀ i, C2927.adjugate i i ≠ 0) := by
  intro h
  have := certificate2927
  rw [h.1] at this
  norm_num at this
def C2928 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2928 : C2928.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2928 : ¬ (C2928.det = 0 ∧ ∀ i, C2928.adjugate i i ≠ 0) := by
  intro h
  have := certificate2928
  rw [h.1] at this
  norm_num at this
def C2929 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2929 : C2929.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2929 : ¬ (C2929.det = 0 ∧ ∀ i, C2929.adjugate i i ≠ 0) := by
  intro h
  have := certificate2929
  rw [h.1] at this
  norm_num at this
def C2930 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2930 : C2930.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2930 : ¬ (C2930.det = 0 ∧ ∀ i, C2930.adjugate i i ≠ 0) := by
  intro h
  have := certificate2930
  rw [h.1] at this
  norm_num at this
def C2931 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2931 : C2931.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2931 : ¬ (C2931.det = 0 ∧ ∀ i, C2931.adjugate i i ≠ 0) := by
  intro h
  have := certificate2931
  rw [h.1] at this
  norm_num at this
def C2932 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2932 : C2932.det = (37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2932 : ¬ (C2932.det = 0 ∧ ∀ i, C2932.adjugate i i ≠ 0) := by
  intro h
  have := certificate2932
  rw [h.1] at this
  norm_num at this
def C2933 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2933 : C2933.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2933 : ¬ (C2933.det = 0 ∧ ∀ i, C2933.adjugate i i ≠ 0) := by
  intro h
  have := certificate2933
  rw [h.1] at this
  norm_num at this
def C2934 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2934 : C2934.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2934 : ¬ (C2934.det = 0 ∧ ∀ i, C2934.adjugate i i ≠ 0) := by
  intro h
  have := certificate2934
  rw [h.1] at this
  norm_num at this
def C2935 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2935 : C2935.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2935 : ¬ (C2935.det = 0 ∧ ∀ i, C2935.adjugate i i ≠ 0) := by
  intro h
  have := certificate2935
  rw [h.1] at this
  norm_num at this
def C2936 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2936 : C2936.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2936 : ¬ (C2936.det = 0 ∧ ∀ i, C2936.adjugate i i ≠ 0) := by
  intro h
  have := certificate2936
  rw [h.1] at this
  norm_num at this
def C2937 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2937 : C2937.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2937 : ¬ (C2937.det = 0 ∧ ∀ i, C2937.adjugate i i ≠ 0) := by
  intro h
  have := certificate2937
  rw [h.1] at this
  norm_num at this
def C2938 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2938 : C2938.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2938 : ¬ (C2938.det = 0 ∧ ∀ i, C2938.adjugate i i ≠ 0) := by
  intro h
  have := certificate2938
  rw [h.1] at this
  norm_num at this
def C2939 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2939 : C2939.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2939 : ¬ (C2939.det = 0 ∧ ∀ i, C2939.adjugate i i ≠ 0) := by
  intro h
  have := certificate2939
  rw [h.1] at this
  norm_num at this
def C2940 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2940 : C2940.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2940 : ¬ (C2940.det = 0 ∧ ∀ i, C2940.adjugate i i ≠ 0) := by
  intro h
  have := certificate2940
  rw [h.1] at this
  norm_num at this
def C2941 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2941 : C2941.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2941 : ¬ (C2941.det = 0 ∧ ∀ i, C2941.adjugate i i ≠ 0) := by
  intro h
  have := certificate2941
  rw [h.1] at this
  norm_num at this
def C2942 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2942 : C2942.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2942 : ¬ (C2942.det = 0 ∧ ∀ i, C2942.adjugate i i ≠ 0) := by
  intro h
  have := certificate2942
  rw [h.1] at this
  norm_num at this
def C2943 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2943 : C2943.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2943 : ¬ (C2943.det = 0 ∧ ∀ i, C2943.adjugate i i ≠ 0) := by
  intro h
  have := certificate2943
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0091
