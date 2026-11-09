import VerifiedDet
namespace Nut8.NewCertificates0191
def C6112 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate6112 : C6112.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6112 : ¬ (C6112.det = 0 ∧ ∀ i, C6112.adjugate i i ≠ 0) := by
  intro h
  have := certificate6112
  rw [h.1] at this
  norm_num at this
def C6113 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate6113 : C6113.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6113 : ¬ (C6113.det = 0 ∧ ∀ i, C6113.adjugate i i ≠ 0) := by
  intro h
  have := certificate6113
  rw [h.1] at this
  norm_num at this
def C6114 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate6114 : C6114.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6114 : ¬ (C6114.det = 0 ∧ ∀ i, C6114.adjugate i i ≠ 0) := by
  intro h
  have := certificate6114
  rw [h.1] at this
  norm_num at this
def C6115 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate6115 : C6115.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6115 : ¬ (C6115.det = 0 ∧ ∀ i, C6115.adjugate i i ≠ 0) := by
  intro h
  have := certificate6115
  rw [h.1] at this
  norm_num at this
def C6116 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate6116 : C6116.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6116 : ¬ (C6116.det = 0 ∧ ∀ i, C6116.adjugate i i ≠ 0) := by
  intro h
  have := certificate6116
  rw [h.1] at this
  norm_num at this
def C6117 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate6117 : C6117.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6117 : ¬ (C6117.det = 0 ∧ ∀ i, C6117.adjugate i i ≠ 0) := by
  intro h
  have := certificate6117
  rw [h.1] at this
  norm_num at this
def C6118 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate6118 : C6118.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6118 : ¬ (C6118.det = 0 ∧ ∀ i, C6118.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6118
def C6119 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate6119 : C6119.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6119 : ¬ (C6119.det = 0 ∧ ∀ i, C6119.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6119
def C6120 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate6120 : C6120.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6120 : ¬ (C6120.det = 0 ∧ ∀ i, C6120.adjugate i i ≠ 0) := by
  intro h
  have := certificate6120
  rw [h.1] at this
  norm_num at this
def C6121 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate6121 : C6121.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6121 : ¬ (C6121.det = 0 ∧ ∀ i, C6121.adjugate i i ≠ 0) := by
  intro h
  have := certificate6121
  rw [h.1] at this
  norm_num at this
def C6122 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate6122 : C6122.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6122 : ¬ (C6122.det = 0 ∧ ∀ i, C6122.adjugate i i ≠ 0) := by
  intro h
  have := certificate6122
  rw [h.1] at this
  norm_num at this
def C6123 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate6123 : C6123.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6123 : ¬ (C6123.det = 0 ∧ ∀ i, C6123.adjugate i i ≠ 0) := by
  intro h
  have := certificate6123
  rw [h.1] at this
  norm_num at this
def C6124 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate6124 : C6124.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6124 : ¬ (C6124.det = 0 ∧ ∀ i, C6124.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6124
def C6125 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate6125 : C6125.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6125 : ¬ (C6125.det = 0 ∧ ∀ i, C6125.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6125
def C6126 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate6126 : C6126.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6126 : ¬ (C6126.det = 0 ∧ ∀ i, C6126.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6126
def C6127 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate6127 : C6127.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6127 : ¬ (C6127.det = 0 ∧ ∀ i, C6127.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6127
def C6128 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate6128 : C6128.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6128 : ¬ (C6128.det = 0 ∧ ∀ i, C6128.adjugate i i ≠ 0) := by
  intro h
  have := certificate6128
  rw [h.1] at this
  norm_num at this
def C6129 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate6129 : C6129.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6129 : ¬ (C6129.det = 0 ∧ ∀ i, C6129.adjugate i i ≠ 0) := by
  intro h
  have := certificate6129
  rw [h.1] at this
  norm_num at this
def C6130 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate6130 : C6130.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6130 : ¬ (C6130.det = 0 ∧ ∀ i, C6130.adjugate i i ≠ 0) := by
  intro h
  have := certificate6130
  rw [h.1] at this
  norm_num at this
def C6131 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate6131 : C6131.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6131 : ¬ (C6131.det = 0 ∧ ∀ i, C6131.adjugate i i ≠ 0) := by
  intro h
  have := certificate6131
  rw [h.1] at this
  norm_num at this
def C6132 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate6132 : C6132.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6132 : ¬ (C6132.det = 0 ∧ ∀ i, C6132.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6132
def C6133 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate6133 : C6133.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6133 : ¬ (C6133.det = 0 ∧ ∀ i, C6133.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6133
def C6134 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate6134 : C6134.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6134 : ¬ (C6134.det = 0 ∧ ∀ i, C6134.adjugate i i ≠ 0) := by
  intro h
  have := certificate6134
  rw [h.1] at this
  norm_num at this
def C6135 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate6135 : C6135.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6135 : ¬ (C6135.det = 0 ∧ ∀ i, C6135.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate6135
def C6136 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate6136 : C6136.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6136 : ¬ (C6136.det = 0 ∧ ∀ i, C6136.adjugate i i ≠ 0) := by
  intro h
  have := certificate6136
  rw [h.1] at this
  norm_num at this
def C6137 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate6137 : C6137.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6137 : ¬ (C6137.det = 0 ∧ ∀ i, C6137.adjugate i i ≠ 0) := by
  intro h
  have := certificate6137
  rw [h.1] at this
  norm_num at this
def C6138 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate6138 : C6138.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6138 : ¬ (C6138.det = 0 ∧ ∀ i, C6138.adjugate i i ≠ 0) := by
  intro h
  have := certificate6138
  rw [h.1] at this
  norm_num at this
def C6139 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate6139 : C6139.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6139 : ¬ (C6139.det = 0 ∧ ∀ i, C6139.adjugate i i ≠ 0) := by
  intro h
  have := certificate6139
  rw [h.1] at this
  norm_num at this
def C6140 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate6140 : C6140.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6140 : ¬ (C6140.det = 0 ∧ ∀ i, C6140.adjugate i i ≠ 0) := by
  intro h
  have := certificate6140
  rw [h.1] at this
  norm_num at this
def C6141 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate6141 : C6141.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6141 : ¬ (C6141.det = 0 ∧ ∀ i, C6141.adjugate i i ≠ 0) := by
  intro h
  have := certificate6141
  rw [h.1] at this
  norm_num at this
def C6142 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate6142 : C6142.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6142 : ¬ (C6142.det = 0 ∧ ∀ i, C6142.adjugate i i ≠ 0) := by
  intro h
  have := certificate6142
  rw [h.1] at this
  norm_num at this
def C6143 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate6143 : C6143.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6143 : ¬ (C6143.det = 0 ∧ ∀ i, C6143.adjugate i i ≠ 0) := by
  intro h
  have := certificate6143
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0191
