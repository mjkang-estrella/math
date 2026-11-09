import VerifiedDet
namespace Nut8.NewCertificates0092
def C2944 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2944 : C2944.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2944 : ¬ (C2944.det = 0 ∧ ∀ i, C2944.adjugate i i ≠ 0) := by
  intro h
  have := certificate2944
  rw [h.1] at this
  norm_num at this
def C2945 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2945 : C2945.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2945 : ¬ (C2945.det = 0 ∧ ∀ i, C2945.adjugate i i ≠ 0) := by
  intro h
  have := certificate2945
  rw [h.1] at this
  norm_num at this
def C2946 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2946 : C2946.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2946 : ¬ (C2946.det = 0 ∧ ∀ i, C2946.adjugate i i ≠ 0) := by
  intro h
  have := certificate2946
  rw [h.1] at this
  norm_num at this
def C2947 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2947 : C2947.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2947 : ¬ (C2947.det = 0 ∧ ∀ i, C2947.adjugate i i ≠ 0) := by
  intro h
  have := certificate2947
  rw [h.1] at this
  norm_num at this
def C2948 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2948 : C2948.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2948 : ¬ (C2948.det = 0 ∧ ∀ i, C2948.adjugate i i ≠ 0) := by
  intro h
  have := certificate2948
  rw [h.1] at this
  norm_num at this
def C2949 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2949 : C2949.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2949 : ¬ (C2949.det = 0 ∧ ∀ i, C2949.adjugate i i ≠ 0) := by
  intro h
  have := certificate2949
  rw [h.1] at this
  norm_num at this
def C2950 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2950 : C2950.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2950 : ¬ (C2950.det = 0 ∧ ∀ i, C2950.adjugate i i ≠ 0) := by
  intro h
  have := certificate2950
  rw [h.1] at this
  norm_num at this
def C2951 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2951 : C2951.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2951 : ¬ (C2951.det = 0 ∧ ∀ i, C2951.adjugate i i ≠ 0) := by
  intro h
  have := certificate2951
  rw [h.1] at this
  norm_num at this
def C2952 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2952 : C2952.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2952 : ¬ (C2952.det = 0 ∧ ∀ i, C2952.adjugate i i ≠ 0) := by
  intro h
  have := certificate2952
  rw [h.1] at this
  norm_num at this
def C2953 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2953 : C2953.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2953 : ¬ (C2953.det = 0 ∧ ∀ i, C2953.adjugate i i ≠ 0) := by
  intro h
  have := certificate2953
  rw [h.1] at this
  norm_num at this
def C2954 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2954 : C2954.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2954 : ¬ (C2954.det = 0 ∧ ∀ i, C2954.adjugate i i ≠ 0) := by
  intro h
  have := certificate2954
  rw [h.1] at this
  norm_num at this
def C2955 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2955 : C2955.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2955 : ¬ (C2955.det = 0 ∧ ∀ i, C2955.adjugate i i ≠ 0) := by
  intro h
  have := certificate2955
  rw [h.1] at this
  norm_num at this
def C2956 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2956 : C2956.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2956 : ¬ (C2956.det = 0 ∧ ∀ i, C2956.adjugate i i ≠ 0) := by
  intro h
  have := certificate2956
  rw [h.1] at this
  norm_num at this
def C2957 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2957 : C2957.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2957 : ¬ (C2957.det = 0 ∧ ∀ i, C2957.adjugate i i ≠ 0) := by
  intro h
  have := certificate2957
  rw [h.1] at this
  norm_num at this
def C2958 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2958 : C2958.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2958 : ¬ (C2958.det = 0 ∧ ∀ i, C2958.adjugate i i ≠ 0) := by
  intro h
  have := certificate2958
  rw [h.1] at this
  norm_num at this
def C2959 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2959 : C2959.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2959 : ¬ (C2959.det = 0 ∧ ∀ i, C2959.adjugate i i ≠ 0) := by
  intro h
  have := certificate2959
  rw [h.1] at this
  norm_num at this
def C2960 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2960 : C2960.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2960 : ¬ (C2960.det = 0 ∧ ∀ i, C2960.adjugate i i ≠ 0) := by
  intro h
  have := certificate2960
  rw [h.1] at this
  norm_num at this
def C2961 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2961 : C2961.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2961 : ¬ (C2961.det = 0 ∧ ∀ i, C2961.adjugate i i ≠ 0) := by
  intro h
  have := certificate2961
  rw [h.1] at this
  norm_num at this
def C2962 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2962 : C2962.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2962 : ¬ (C2962.det = 0 ∧ ∀ i, C2962.adjugate i i ≠ 0) := by
  intro h
  have := certificate2962
  rw [h.1] at this
  norm_num at this
def C2963 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2963 : C2963.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2963 : ¬ (C2963.det = 0 ∧ ∀ i, C2963.adjugate i i ≠ 0) := by
  intro h
  have := certificate2963
  rw [h.1] at this
  norm_num at this
def C2964 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2964 : C2964.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2964 : ¬ (C2964.det = 0 ∧ ∀ i, C2964.adjugate i i ≠ 0) := by
  intro h
  have := certificate2964
  rw [h.1] at this
  norm_num at this
def C2965 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2965 : C2965.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2965 : ¬ (C2965.det = 0 ∧ ∀ i, C2965.adjugate i i ≠ 0) := by
  intro h
  have := certificate2965
  rw [h.1] at this
  norm_num at this
def C2966 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2966 : C2966.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2966 : ¬ (C2966.det = 0 ∧ ∀ i, C2966.adjugate i i ≠ 0) := by
  intro h
  have := certificate2966
  rw [h.1] at this
  norm_num at this
def C2967 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2967 : C2967.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2967 : ¬ (C2967.det = 0 ∧ ∀ i, C2967.adjugate i i ≠ 0) := by
  intro h
  have := certificate2967
  rw [h.1] at this
  norm_num at this
def C2968 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2968 : C2968.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2968 : ¬ (C2968.det = 0 ∧ ∀ i, C2968.adjugate i i ≠ 0) := by
  intro h
  have := certificate2968
  rw [h.1] at this
  norm_num at this
def C2969 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2969 : C2969.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2969 : ¬ (C2969.det = 0 ∧ ∀ i, C2969.adjugate i i ≠ 0) := by
  intro h
  have := certificate2969
  rw [h.1] at this
  norm_num at this
def C2970 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2970 : C2970.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2970 : ¬ (C2970.det = 0 ∧ ∀ i, C2970.adjugate i i ≠ 0) := by
  intro h
  have := certificate2970
  rw [h.1] at this
  norm_num at this
def C2971 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2971 : C2971.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2971 : ¬ (C2971.det = 0 ∧ ∀ i, C2971.adjugate i i ≠ 0) := by
  intro h
  have := certificate2971
  rw [h.1] at this
  norm_num at this
def C2972 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2972 : C2972.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2972 : ¬ (C2972.det = 0 ∧ ∀ i, C2972.adjugate i i ≠ 0) := by
  intro h
  have := certificate2972
  rw [h.1] at this
  norm_num at this
def C2973 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2973 : C2973.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2973 : ¬ (C2973.det = 0 ∧ ∀ i, C2973.adjugate i i ≠ 0) := by
  intro h
  have := certificate2973
  rw [h.1] at this
  norm_num at this
def C2974 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2974 : C2974.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2974 : ¬ (C2974.det = 0 ∧ ∀ i, C2974.adjugate i i ≠ 0) := by
  intro h
  have := certificate2974
  rw [h.1] at this
  norm_num at this
def C2975 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2975 : C2975.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2975 : ¬ (C2975.det = 0 ∧ ∀ i, C2975.adjugate i i ≠ 0) := by
  intro h
  have := certificate2975
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0092
