import VerifiedDet
namespace Nut8.NewCertificates0248
def C7936 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7936 : C7936.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7936 : ¬ (C7936.det = 0 ∧ ∀ i, C7936.adjugate i i ≠ 0) := by
  intro h
  have := certificate7936
  rw [h.1] at this
  norm_num at this
def C7937 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7937 : C7937.det = (30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7937 : ¬ (C7937.det = 0 ∧ ∀ i, C7937.adjugate i i ≠ 0) := by
  intro h
  have := certificate7937
  rw [h.1] at this
  norm_num at this
def C7938 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7938 : C7938.det = (70 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7938 : ¬ (C7938.det = 0 ∧ ∀ i, C7938.adjugate i i ≠ 0) := by
  intro h
  have := certificate7938
  rw [h.1] at this
  norm_num at this
def C7939 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7939 : C7939.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7939 : ¬ (C7939.det = 0 ∧ ∀ i, C7939.adjugate i i ≠ 0) := by
  intro h
  have := certificate7939
  rw [h.1] at this
  norm_num at this
def C7940 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7940 : C7940.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7940 : ¬ (C7940.det = 0 ∧ ∀ i, C7940.adjugate i i ≠ 0) := by
  intro h
  have := certificate7940
  rw [h.1] at this
  norm_num at this
def C7941 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7941 : C7941.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7941 : ¬ (C7941.det = 0 ∧ ∀ i, C7941.adjugate i i ≠ 0) := by
  intro h
  have := certificate7941
  rw [h.1] at this
  norm_num at this
def C7942 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7942 : C7942.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7942 : ¬ (C7942.det = 0 ∧ ∀ i, C7942.adjugate i i ≠ 0) := by
  intro h
  have := certificate7942
  rw [h.1] at this
  norm_num at this
def C7943 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7943 : C7943.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7943 : ¬ (C7943.det = 0 ∧ ∀ i, C7943.adjugate i i ≠ 0) := by
  intro h
  have := certificate7943
  rw [h.1] at this
  norm_num at this
def C7944 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate7944 : C7944.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7944 : ¬ (C7944.det = 0 ∧ ∀ i, C7944.adjugate i i ≠ 0) := by
  intro h
  have := certificate7944
  rw [h.1] at this
  norm_num at this
def C7945 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate7945 : C7945.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7945 : ¬ (C7945.det = 0 ∧ ∀ i, C7945.adjugate i i ≠ 0) := by
  intro h
  have := certificate7945
  rw [h.1] at this
  norm_num at this
def C7946 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate7946 : C7946.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7946 : ¬ (C7946.det = 0 ∧ ∀ i, C7946.adjugate i i ≠ 0) := by
  intro h
  have := certificate7946
  rw [h.1] at this
  norm_num at this
def C7947 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate7947 : C7947.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7947 : ¬ (C7947.det = 0 ∧ ∀ i, C7947.adjugate i i ≠ 0) := by
  intro h
  have := certificate7947
  rw [h.1] at this
  norm_num at this
def C7948 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7948 : C7948.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7948 : ¬ (C7948.det = 0 ∧ ∀ i, C7948.adjugate i i ≠ 0) := by
  intro h
  have := certificate7948
  rw [h.1] at this
  norm_num at this
def C7949 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7949 : C7949.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7949 : ¬ (C7949.det = 0 ∧ ∀ i, C7949.adjugate i i ≠ 0) := by
  intro h
  have := certificate7949
  rw [h.1] at this
  norm_num at this
def C7950 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7950 : C7950.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7950 : ¬ (C7950.det = 0 ∧ ∀ i, C7950.adjugate i i ≠ 0) := by
  intro h
  have := certificate7950
  rw [h.1] at this
  norm_num at this
def C7951 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7951 : C7951.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7951 : ¬ (C7951.det = 0 ∧ ∀ i, C7951.adjugate i i ≠ 0) := by
  intro h
  have := certificate7951
  rw [h.1] at this
  norm_num at this
def C7952 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7952 : C7952.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7952 : ¬ (C7952.det = 0 ∧ ∀ i, C7952.adjugate i i ≠ 0) := by
  intro h
  have := certificate7952
  rw [h.1] at this
  norm_num at this
def C7953 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate7953 : C7953.det = (75 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7953 : ¬ (C7953.det = 0 ∧ ∀ i, C7953.adjugate i i ≠ 0) := by
  intro h
  have := certificate7953
  rw [h.1] at this
  norm_num at this
def C7954 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7954 : C7954.det = (75 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7954 : ¬ (C7954.det = 0 ∧ ∀ i, C7954.adjugate i i ≠ 0) := by
  intro h
  have := certificate7954
  rw [h.1] at this
  norm_num at this
def C7955 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate7955 : C7955.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7955 : ¬ (C7955.det = 0 ∧ ∀ i, C7955.adjugate i i ≠ 0) := by
  intro h
  have := certificate7955
  rw [h.1] at this
  norm_num at this
def C7956 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7956 : C7956.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7956 : ¬ (C7956.det = 0 ∧ ∀ i, C7956.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7956
def C7957 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7957 : C7957.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7957 : ¬ (C7957.det = 0 ∧ ∀ i, C7957.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7957
def C7958 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7958 : C7958.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7958 : ¬ (C7958.det = 0 ∧ ∀ i, C7958.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7958
def C7959 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7959 : C7959.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7959 : ¬ (C7959.det = 0 ∧ ∀ i, C7959.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7959
def C7960 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7960 : C7960.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7960 : ¬ (C7960.det = 0 ∧ ∀ i, C7960.adjugate i i ≠ 0) := by
  intro h
  have := certificate7960
  rw [h.1] at this
  norm_num at this
def C7961 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7961 : C7961.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7961 : ¬ (C7961.det = 0 ∧ ∀ i, C7961.adjugate i i ≠ 0) := by
  intro h
  have := certificate7961
  rw [h.1] at this
  norm_num at this
def C7962 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7962 : C7962.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7962 : ¬ (C7962.det = 0 ∧ ∀ i, C7962.adjugate i i ≠ 0) := by
  intro h
  have := certificate7962
  rw [h.1] at this
  norm_num at this
def C7963 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7963 : C7963.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7963 : ¬ (C7963.det = 0 ∧ ∀ i, C7963.adjugate i i ≠ 0) := by
  intro h
  have := certificate7963
  rw [h.1] at this
  norm_num at this
def C7964 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7964 : C7964.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7964 : ¬ (C7964.det = 0 ∧ ∀ i, C7964.adjugate i i ≠ 0) := by
  intro h
  have := certificate7964
  rw [h.1] at this
  norm_num at this
def C7965 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7965 : C7965.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7965 : ¬ (C7965.det = 0 ∧ ∀ i, C7965.adjugate i i ≠ 0) := by
  intro h
  have := certificate7965
  rw [h.1] at this
  norm_num at this
def C7966 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7966 : C7966.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7966 : ¬ (C7966.det = 0 ∧ ∀ i, C7966.adjugate i i ≠ 0) := by
  intro h
  have := certificate7966
  rw [h.1] at this
  norm_num at this
def C7967 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7967 : C7967.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7967 : ¬ (C7967.det = 0 ∧ ∀ i, C7967.adjugate i i ≠ 0) := by
  intro h
  have := certificate7967
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0248
