import VerifiedDet
namespace Nut8.NewCertificates0093
def C2976 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2976 : C2976.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2976 : ¬ (C2976.det = 0 ∧ ∀ i, C2976.adjugate i i ≠ 0) := by
  intro h
  have := certificate2976
  rw [h.1] at this
  norm_num at this
def C2977 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2977 : C2977.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2977 : ¬ (C2977.det = 0 ∧ ∀ i, C2977.adjugate i i ≠ 0) := by
  intro h
  have := certificate2977
  rw [h.1] at this
  norm_num at this
def C2978 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2978 : C2978.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2978 : ¬ (C2978.det = 0 ∧ ∀ i, C2978.adjugate i i ≠ 0) := by
  intro h
  have := certificate2978
  rw [h.1] at this
  norm_num at this
def C2979 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2979 : C2979.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2979 : ¬ (C2979.det = 0 ∧ ∀ i, C2979.adjugate i i ≠ 0) := by
  intro h
  have := certificate2979
  rw [h.1] at this
  norm_num at this
def C2980 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2980 : C2980.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2980 : ¬ (C2980.det = 0 ∧ ∀ i, C2980.adjugate i i ≠ 0) := by
  intro h
  have := certificate2980
  rw [h.1] at this
  norm_num at this
def C2981 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2981 : C2981.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2981 : ¬ (C2981.det = 0 ∧ ∀ i, C2981.adjugate i i ≠ 0) := by
  intro h
  have := certificate2981
  rw [h.1] at this
  norm_num at this
def C2982 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2982 : C2982.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2982 : ¬ (C2982.det = 0 ∧ ∀ i, C2982.adjugate i i ≠ 0) := by
  intro h
  have := certificate2982
  rw [h.1] at this
  norm_num at this
def C2983 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2983 : C2983.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2983 : ¬ (C2983.det = 0 ∧ ∀ i, C2983.adjugate i i ≠ 0) := by
  intro h
  have := certificate2983
  rw [h.1] at this
  norm_num at this
def C2984 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2984 : C2984.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2984 : ¬ (C2984.det = 0 ∧ ∀ i, C2984.adjugate i i ≠ 0) := by
  intro h
  have := certificate2984
  rw [h.1] at this
  norm_num at this
def C2985 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2985 : C2985.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2985 : ¬ (C2985.det = 0 ∧ ∀ i, C2985.adjugate i i ≠ 0) := by
  intro h
  have := certificate2985
  rw [h.1] at this
  norm_num at this
def C2986 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2986 : C2986.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2986 : ¬ (C2986.det = 0 ∧ ∀ i, C2986.adjugate i i ≠ 0) := by
  intro h
  have := certificate2986
  rw [h.1] at this
  norm_num at this
def C2987 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2987 : C2987.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2987 : ¬ (C2987.det = 0 ∧ ∀ i, C2987.adjugate i i ≠ 0) := by
  intro h
  have := certificate2987
  rw [h.1] at this
  norm_num at this
def C2988 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2988 : C2988.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2988 : ¬ (C2988.det = 0 ∧ ∀ i, C2988.adjugate i i ≠ 0) := by
  intro h
  have := certificate2988
  rw [h.1] at this
  norm_num at this
def C2989 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2989 : C2989.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2989 : ¬ (C2989.det = 0 ∧ ∀ i, C2989.adjugate i i ≠ 0) := by
  intro h
  have := certificate2989
  rw [h.1] at this
  norm_num at this
def C2990 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2990 : C2990.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2990 : ¬ (C2990.det = 0 ∧ ∀ i, C2990.adjugate i i ≠ 0) := by
  intro h
  have := certificate2990
  rw [h.1] at this
  norm_num at this
def C2991 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2991 : C2991.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2991 : ¬ (C2991.det = 0 ∧ ∀ i, C2991.adjugate i i ≠ 0) := by
  intro h
  have := certificate2991
  rw [h.1] at this
  norm_num at this
def C2992 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2992 : C2992.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2992 : ¬ (C2992.det = 0 ∧ ∀ i, C2992.adjugate i i ≠ 0) := by
  intro h
  have := certificate2992
  rw [h.1] at this
  norm_num at this
def C2993 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2993 : C2993.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2993 : ¬ (C2993.det = 0 ∧ ∀ i, C2993.adjugate i i ≠ 0) := by
  intro h
  have := certificate2993
  rw [h.1] at this
  norm_num at this
def C2994 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2994 : C2994.det = (-70 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2994 : ¬ (C2994.det = 0 ∧ ∀ i, C2994.adjugate i i ≠ 0) := by
  intro h
  have := certificate2994
  rw [h.1] at this
  norm_num at this
def C2995 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2995 : C2995.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2995 : ¬ (C2995.det = 0 ∧ ∀ i, C2995.adjugate i i ≠ 0) := by
  intro h
  have := certificate2995
  rw [h.1] at this
  norm_num at this
def C2996 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2996 : C2996.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2996 : ¬ (C2996.det = 0 ∧ ∀ i, C2996.adjugate i i ≠ 0) := by
  intro h
  have := certificate2996
  rw [h.1] at this
  norm_num at this
def C2997 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2997 : C2997.det = (-70 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2997 : ¬ (C2997.det = 0 ∧ ∀ i, C2997.adjugate i i ≠ 0) := by
  intro h
  have := certificate2997
  rw [h.1] at this
  norm_num at this
def C2998 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2998 : C2998.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2998 : ¬ (C2998.det = 0 ∧ ∀ i, C2998.adjugate i i ≠ 0) := by
  intro h
  have := certificate2998
  rw [h.1] at this
  norm_num at this
def C2999 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2999 : C2999.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2999 : ¬ (C2999.det = 0 ∧ ∀ i, C2999.adjugate i i ≠ 0) := by
  intro h
  have := certificate2999
  rw [h.1] at this
  norm_num at this
def C3000 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3000 : C3000.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3000 : ¬ (C3000.det = 0 ∧ ∀ i, C3000.adjugate i i ≠ 0) := by
  intro h
  have := certificate3000
  rw [h.1] at this
  norm_num at this
def C3001 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3001 : C3001.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3001 : ¬ (C3001.det = 0 ∧ ∀ i, C3001.adjugate i i ≠ 0) := by
  intro h
  have := certificate3001
  rw [h.1] at this
  norm_num at this
def C3002 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3002 : C3002.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3002 : ¬ (C3002.det = 0 ∧ ∀ i, C3002.adjugate i i ≠ 0) := by
  intro h
  have := certificate3002
  rw [h.1] at this
  norm_num at this
def C3003 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3003 : C3003.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3003 : ¬ (C3003.det = 0 ∧ ∀ i, C3003.adjugate i i ≠ 0) := by
  intro h
  have := certificate3003
  rw [h.1] at this
  norm_num at this
def C3004 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3004 : C3004.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3004 : ¬ (C3004.det = 0 ∧ ∀ i, C3004.adjugate i i ≠ 0) := by
  intro h
  have := certificate3004
  rw [h.1] at this
  norm_num at this
def C3005 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3005 : C3005.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3005 : ¬ (C3005.det = 0 ∧ ∀ i, C3005.adjugate i i ≠ 0) := by
  intro h
  have := certificate3005
  rw [h.1] at this
  norm_num at this
def C3006 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3006 : C3006.det = (-85 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3006 : ¬ (C3006.det = 0 ∧ ∀ i, C3006.adjugate i i ≠ 0) := by
  intro h
  have := certificate3006
  rw [h.1] at this
  norm_num at this
def C3007 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3007 : C3007.det = (-45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3007 : ¬ (C3007.det = 0 ∧ ∀ i, C3007.adjugate i i ≠ 0) := by
  intro h
  have := certificate3007
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0093
