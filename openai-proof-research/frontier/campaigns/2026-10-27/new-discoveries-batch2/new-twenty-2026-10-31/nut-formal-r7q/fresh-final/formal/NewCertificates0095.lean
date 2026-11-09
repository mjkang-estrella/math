import VerifiedDet
namespace Nut8.NewCertificates0095
def C3040 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3040 : C3040.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3040 : ¬ (C3040.det = 0 ∧ ∀ i, C3040.adjugate i i ≠ 0) := by
  intro h
  have := certificate3040
  rw [h.1] at this
  norm_num at this
def C3041 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3041 : C3041.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3041 : ¬ (C3041.det = 0 ∧ ∀ i, C3041.adjugate i i ≠ 0) := by
  intro h
  have := certificate3041
  rw [h.1] at this
  norm_num at this
def C3042 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3042 : C3042.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3042 : ¬ (C3042.det = 0 ∧ ∀ i, C3042.adjugate i i ≠ 0) := by
  intro h
  have := certificate3042
  rw [h.1] at this
  norm_num at this
def C3043 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3043 : C3043.det = (54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3043 : ¬ (C3043.det = 0 ∧ ∀ i, C3043.adjugate i i ≠ 0) := by
  intro h
  have := certificate3043
  rw [h.1] at this
  norm_num at this
def C3044 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3044 : C3044.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3044 : ¬ (C3044.det = 0 ∧ ∀ i, C3044.adjugate i i ≠ 0) := by
  intro h
  have := certificate3044
  rw [h.1] at this
  norm_num at this
def C3045 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3045 : C3045.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3045 : ¬ (C3045.det = 0 ∧ ∀ i, C3045.adjugate i i ≠ 0) := by
  intro h
  have := certificate3045
  rw [h.1] at this
  norm_num at this
def C3046 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3046 : C3046.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3046 : ¬ (C3046.det = 0 ∧ ∀ i, C3046.adjugate i i ≠ 0) := by
  intro h
  have := certificate3046
  rw [h.1] at this
  norm_num at this
def C3047 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3047 : C3047.det = (34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3047 : ¬ (C3047.det = 0 ∧ ∀ i, C3047.adjugate i i ≠ 0) := by
  intro h
  have := certificate3047
  rw [h.1] at this
  norm_num at this
def C3048 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3048 : C3048.det = (54 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3048 : ¬ (C3048.det = 0 ∧ ∀ i, C3048.adjugate i i ≠ 0) := by
  intro h
  have := certificate3048
  rw [h.1] at this
  norm_num at this
def C3049 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3049 : C3049.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3049 : ¬ (C3049.det = 0 ∧ ∀ i, C3049.adjugate i i ≠ 0) := by
  intro h
  have := certificate3049
  rw [h.1] at this
  norm_num at this
def C3050 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3050 : C3050.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3050 : ¬ (C3050.det = 0 ∧ ∀ i, C3050.adjugate i i ≠ 0) := by
  intro h
  have := certificate3050
  rw [h.1] at this
  norm_num at this
def C3051 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate3051 : C3051.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3051 : ¬ (C3051.det = 0 ∧ ∀ i, C3051.adjugate i i ≠ 0) := by
  intro h
  have := certificate3051
  rw [h.1] at this
  norm_num at this
def C3052 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3052 : C3052.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3052 : ¬ (C3052.det = 0 ∧ ∀ i, C3052.adjugate i i ≠ 0) := by
  intro h
  have := certificate3052
  rw [h.1] at this
  norm_num at this
def C3053 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate3053 : C3053.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3053 : ¬ (C3053.det = 0 ∧ ∀ i, C3053.adjugate i i ≠ 0) := by
  intro h
  have := certificate3053
  rw [h.1] at this
  norm_num at this
def C3054 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3054 : C3054.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3054 : ¬ (C3054.det = 0 ∧ ∀ i, C3054.adjugate i i ≠ 0) := by
  intro h
  have := certificate3054
  rw [h.1] at this
  norm_num at this
def C3055 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3055 : C3055.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3055 : ¬ (C3055.det = 0 ∧ ∀ i, C3055.adjugate i i ≠ 0) := by
  intro h
  have := certificate3055
  rw [h.1] at this
  norm_num at this
def C3056 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3056 : C3056.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3056 : ¬ (C3056.det = 0 ∧ ∀ i, C3056.adjugate i i ≠ 0) := by
  intro h
  have := certificate3056
  rw [h.1] at this
  norm_num at this
def C3057 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3057 : C3057.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3057 : ¬ (C3057.det = 0 ∧ ∀ i, C3057.adjugate i i ≠ 0) := by
  intro h
  have := certificate3057
  rw [h.1] at this
  norm_num at this
def C3058 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3058 : C3058.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3058 : ¬ (C3058.det = 0 ∧ ∀ i, C3058.adjugate i i ≠ 0) := by
  intro h
  have := certificate3058
  rw [h.1] at this
  norm_num at this
def C3059 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3059 : C3059.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3059 : ¬ (C3059.det = 0 ∧ ∀ i, C3059.adjugate i i ≠ 0) := by
  intro h
  have := certificate3059
  rw [h.1] at this
  norm_num at this
def C3060 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate3060 : C3060.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3060 : ¬ (C3060.det = 0 ∧ ∀ i, C3060.adjugate i i ≠ 0) := by
  intro h
  have := certificate3060
  rw [h.1] at this
  norm_num at this
def C3061 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate3061 : C3061.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3061 : ¬ (C3061.det = 0 ∧ ∀ i, C3061.adjugate i i ≠ 0) := by
  intro h
  have := certificate3061
  rw [h.1] at this
  norm_num at this
def C3062 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3062 : C3062.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3062 : ¬ (C3062.det = 0 ∧ ∀ i, C3062.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3062
def C3063 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3063 : C3063.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3063 : ¬ (C3063.det = 0 ∧ ∀ i, C3063.adjugate i i ≠ 0) := by
  intro h
  have := certificate3063
  rw [h.1] at this
  norm_num at this
def C3064 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3064 : C3064.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3064 : ¬ (C3064.det = 0 ∧ ∀ i, C3064.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3064
def C3065 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3065 : C3065.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3065 : ¬ (C3065.det = 0 ∧ ∀ i, C3065.adjugate i i ≠ 0) := by
  intro h
  have := certificate3065
  rw [h.1] at this
  norm_num at this
def C3066 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3066 : C3066.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3066 : ¬ (C3066.det = 0 ∧ ∀ i, C3066.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3066
def C3067 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3067 : C3067.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3067 : ¬ (C3067.det = 0 ∧ ∀ i, C3067.adjugate i i ≠ 0) := by
  intro h
  have := certificate3067
  rw [h.1] at this
  norm_num at this
def C3068 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3068 : C3068.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3068 : ¬ (C3068.det = 0 ∧ ∀ i, C3068.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3068
def C3069 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3069 : C3069.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3069 : ¬ (C3069.det = 0 ∧ ∀ i, C3069.adjugate i i ≠ 0) := by
  intro h
  have := certificate3069
  rw [h.1] at this
  norm_num at this
def C3070 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate3070 : C3070.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3070 : ¬ (C3070.det = 0 ∧ ∀ i, C3070.adjugate i i ≠ 0) := by
  intro h
  have := certificate3070
  rw [h.1] at this
  norm_num at this
def C3071 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate3071 : C3071.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3071 : ¬ (C3071.det = 0 ∧ ∀ i, C3071.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3071
end Nut8.NewCertificates0095
