import VerifiedDet
namespace Nut8.NewCertificates0190
def C6080 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6080 : C6080.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6080 : ¬ (C6080.det = 0 ∧ ∀ i, C6080.adjugate i i ≠ 0) := by
  intro h
  have := certificate6080
  rw [h.1] at this
  norm_num at this
def C6081 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6081 : C6081.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6081 : ¬ (C6081.det = 0 ∧ ∀ i, C6081.adjugate i i ≠ 0) := by
  intro h
  have := certificate6081
  rw [h.1] at this
  norm_num at this
def C6082 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6082 : C6082.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6082 : ¬ (C6082.det = 0 ∧ ∀ i, C6082.adjugate i i ≠ 0) := by
  intro h
  have := certificate6082
  rw [h.1] at this
  norm_num at this
def C6083 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6083 : C6083.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6083 : ¬ (C6083.det = 0 ∧ ∀ i, C6083.adjugate i i ≠ 0) := by
  intro h
  have := certificate6083
  rw [h.1] at this
  norm_num at this
def C6084 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6084 : C6084.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6084 : ¬ (C6084.det = 0 ∧ ∀ i, C6084.adjugate i i ≠ 0) := by
  intro h
  have := certificate6084
  rw [h.1] at this
  norm_num at this
def C6085 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6085 : C6085.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6085 : ¬ (C6085.det = 0 ∧ ∀ i, C6085.adjugate i i ≠ 0) := by
  intro h
  have := certificate6085
  rw [h.1] at this
  norm_num at this
def C6086 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6086 : C6086.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6086 : ¬ (C6086.det = 0 ∧ ∀ i, C6086.adjugate i i ≠ 0) := by
  intro h
  have := certificate6086
  rw [h.1] at this
  norm_num at this
def C6087 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6087 : C6087.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6087 : ¬ (C6087.det = 0 ∧ ∀ i, C6087.adjugate i i ≠ 0) := by
  intro h
  have := certificate6087
  rw [h.1] at this
  norm_num at this
def C6088 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6088 : C6088.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6088 : ¬ (C6088.det = 0 ∧ ∀ i, C6088.adjugate i i ≠ 0) := by
  intro h
  have := certificate6088
  rw [h.1] at this
  norm_num at this
def C6089 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6089 : C6089.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6089 : ¬ (C6089.det = 0 ∧ ∀ i, C6089.adjugate i i ≠ 0) := by
  intro h
  have := certificate6089
  rw [h.1] at this
  norm_num at this
def C6090 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6090 : C6090.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6090 : ¬ (C6090.det = 0 ∧ ∀ i, C6090.adjugate i i ≠ 0) := by
  intro h
  have := certificate6090
  rw [h.1] at this
  norm_num at this
def C6091 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6091 : C6091.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6091 : ¬ (C6091.det = 0 ∧ ∀ i, C6091.adjugate i i ≠ 0) := by
  intro h
  have := certificate6091
  rw [h.1] at this
  norm_num at this
def C6092 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6092 : C6092.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6092 : ¬ (C6092.det = 0 ∧ ∀ i, C6092.adjugate i i ≠ 0) := by
  intro h
  have := certificate6092
  rw [h.1] at this
  norm_num at this
def C6093 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6093 : C6093.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6093 : ¬ (C6093.det = 0 ∧ ∀ i, C6093.adjugate i i ≠ 0) := by
  intro h
  have := certificate6093
  rw [h.1] at this
  norm_num at this
def C6094 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6094 : C6094.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6094 : ¬ (C6094.det = 0 ∧ ∀ i, C6094.adjugate i i ≠ 0) := by
  intro h
  have := certificate6094
  rw [h.1] at this
  norm_num at this
def C6095 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6095 : C6095.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6095 : ¬ (C6095.det = 0 ∧ ∀ i, C6095.adjugate i i ≠ 0) := by
  intro h
  have := certificate6095
  rw [h.1] at this
  norm_num at this
def C6096 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6096 : C6096.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6096 : ¬ (C6096.det = 0 ∧ ∀ i, C6096.adjugate i i ≠ 0) := by
  intro h
  have := certificate6096
  rw [h.1] at this
  norm_num at this
def C6097 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6097 : C6097.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6097 : ¬ (C6097.det = 0 ∧ ∀ i, C6097.adjugate i i ≠ 0) := by
  intro h
  have := certificate6097
  rw [h.1] at this
  norm_num at this
def C6098 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6098 : C6098.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6098 : ¬ (C6098.det = 0 ∧ ∀ i, C6098.adjugate i i ≠ 0) := by
  intro h
  have := certificate6098
  rw [h.1] at this
  norm_num at this
def C6099 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6099 : C6099.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6099 : ¬ (C6099.det = 0 ∧ ∀ i, C6099.adjugate i i ≠ 0) := by
  intro h
  have := certificate6099
  rw [h.1] at this
  norm_num at this
def C6100 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate6100 : C6100.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6100 : ¬ (C6100.det = 0 ∧ ∀ i, C6100.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6100
def C6101 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate6101 : C6101.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6101 : ¬ (C6101.det = 0 ∧ ∀ i, C6101.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6101
def C6102 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate6102 : C6102.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6102 : ¬ (C6102.det = 0 ∧ ∀ i, C6102.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6102
def C6103 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate6103 : C6103.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6103 : ¬ (C6103.det = 0 ∧ ∀ i, C6103.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6103
def C6104 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate6104 : C6104.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6104 : ¬ (C6104.det = 0 ∧ ∀ i, C6104.adjugate i i ≠ 0) := by
  intro h
  have := certificate6104
  rw [h.1] at this
  norm_num at this
def C6105 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate6105 : C6105.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6105 : ¬ (C6105.det = 0 ∧ ∀ i, C6105.adjugate i i ≠ 0) := by
  intro h
  have := certificate6105
  rw [h.1] at this
  norm_num at this
def C6106 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate6106 : C6106.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6106 : ¬ (C6106.det = 0 ∧ ∀ i, C6106.adjugate i i ≠ 0) := by
  intro h
  have := certificate6106
  rw [h.1] at this
  norm_num at this
def C6107 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate6107 : C6107.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6107 : ¬ (C6107.det = 0 ∧ ∀ i, C6107.adjugate i i ≠ 0) := by
  intro h
  have := certificate6107
  rw [h.1] at this
  norm_num at this
def C6108 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate6108 : C6108.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6108 : ¬ (C6108.det = 0 ∧ ∀ i, C6108.adjugate i i ≠ 0) := by
  intro h
  have := certificate6108
  rw [h.1] at this
  norm_num at this
def C6109 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate6109 : C6109.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6109 : ¬ (C6109.det = 0 ∧ ∀ i, C6109.adjugate i i ≠ 0) := by
  intro h
  have := certificate6109
  rw [h.1] at this
  norm_num at this
def C6110 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate6110 : C6110.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6110 : ¬ (C6110.det = 0 ∧ ∀ i, C6110.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6110
def C6111 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate6111 : C6111.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6111 : ¬ (C6111.det = 0 ∧ ∀ i, C6111.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6111
end Nut8.NewCertificates0190
