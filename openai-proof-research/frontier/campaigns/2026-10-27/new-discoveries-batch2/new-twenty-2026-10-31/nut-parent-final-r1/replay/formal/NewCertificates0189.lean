import VerifiedDet
namespace Nut8.NewCertificates0189
def C6048 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6048 : C6048.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6048 : ¬ (C6048.det = 0 ∧ ∀ i, C6048.adjugate i i ≠ 0) := by
  intro h
  have := certificate6048
  rw [h.1] at this
  norm_num at this
def C6049 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6049 : C6049.det = (-27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6049 : ¬ (C6049.det = 0 ∧ ∀ i, C6049.adjugate i i ≠ 0) := by
  intro h
  have := certificate6049
  rw [h.1] at this
  norm_num at this
def C6050 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6050 : C6050.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6050 : ¬ (C6050.det = 0 ∧ ∀ i, C6050.adjugate i i ≠ 0) := by
  intro h
  have := certificate6050
  rw [h.1] at this
  norm_num at this
def C6051 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, -1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6051 : C6051.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6051 : ¬ (C6051.det = 0 ∧ ∀ i, C6051.adjugate i i ≠ 0) := by
  intro h
  have := certificate6051
  rw [h.1] at this
  norm_num at this
def C6052 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6052 : C6052.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6052 : ¬ (C6052.det = 0 ∧ ∀ i, C6052.adjugate i i ≠ 0) := by
  intro h
  have := certificate6052
  rw [h.1] at this
  norm_num at this
def C6053 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6053 : C6053.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6053 : ¬ (C6053.det = 0 ∧ ∀ i, C6053.adjugate i i ≠ 0) := by
  intro h
  have := certificate6053
  rw [h.1] at this
  norm_num at this
def C6054 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6054 : C6054.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6054 : ¬ (C6054.det = 0 ∧ ∀ i, C6054.adjugate i i ≠ 0) := by
  intro h
  have := certificate6054
  rw [h.1] at this
  norm_num at this
def C6055 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6055 : C6055.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6055 : ¬ (C6055.det = 0 ∧ ∀ i, C6055.adjugate i i ≠ 0) := by
  intro h
  have := certificate6055
  rw [h.1] at this
  norm_num at this
def C6056 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6056 : C6056.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6056 : ¬ (C6056.det = 0 ∧ ∀ i, C6056.adjugate i i ≠ 0) := by
  intro h
  have := certificate6056
  rw [h.1] at this
  norm_num at this
def C6057 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6057 : C6057.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6057 : ¬ (C6057.det = 0 ∧ ∀ i, C6057.adjugate i i ≠ 0) := by
  intro h
  have := certificate6057
  rw [h.1] at this
  norm_num at this
def C6058 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6058 : C6058.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6058 : ¬ (C6058.det = 0 ∧ ∀ i, C6058.adjugate i i ≠ 0) := by
  intro h
  have := certificate6058
  rw [h.1] at this
  norm_num at this
def C6059 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6059 : C6059.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6059 : ¬ (C6059.det = 0 ∧ ∀ i, C6059.adjugate i i ≠ 0) := by
  intro h
  have := certificate6059
  rw [h.1] at this
  norm_num at this
def C6060 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6060 : C6060.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6060 : ¬ (C6060.det = 0 ∧ ∀ i, C6060.adjugate i i ≠ 0) := by
  intro h
  have := certificate6060
  rw [h.1] at this
  norm_num at this
def C6061 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6061 : C6061.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6061 : ¬ (C6061.det = 0 ∧ ∀ i, C6061.adjugate i i ≠ 0) := by
  intro h
  have := certificate6061
  rw [h.1] at this
  norm_num at this
def C6062 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6062 : C6062.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6062 : ¬ (C6062.det = 0 ∧ ∀ i, C6062.adjugate i i ≠ 0) := by
  intro h
  have := certificate6062
  rw [h.1] at this
  norm_num at this
def C6063 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6063 : C6063.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6063 : ¬ (C6063.det = 0 ∧ ∀ i, C6063.adjugate i i ≠ 0) := by
  intro h
  have := certificate6063
  rw [h.1] at this
  norm_num at this
def C6064 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6064 : C6064.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6064 : ¬ (C6064.det = 0 ∧ ∀ i, C6064.adjugate i i ≠ 0) := by
  intro h
  have := certificate6064
  rw [h.1] at this
  norm_num at this
def C6065 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6065 : C6065.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6065 : ¬ (C6065.det = 0 ∧ ∀ i, C6065.adjugate i i ≠ 0) := by
  intro h
  have := certificate6065
  rw [h.1] at this
  norm_num at this
def C6066 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6066 : C6066.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6066 : ¬ (C6066.det = 0 ∧ ∀ i, C6066.adjugate i i ≠ 0) := by
  intro h
  have := certificate6066
  rw [h.1] at this
  norm_num at this
def C6067 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6067 : C6067.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6067 : ¬ (C6067.det = 0 ∧ ∀ i, C6067.adjugate i i ≠ 0) := by
  intro h
  have := certificate6067
  rw [h.1] at this
  norm_num at this
def C6068 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6068 : C6068.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6068 : ¬ (C6068.det = 0 ∧ ∀ i, C6068.adjugate i i ≠ 0) := by
  intro h
  have := certificate6068
  rw [h.1] at this
  norm_num at this
def C6069 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6069 : C6069.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6069 : ¬ (C6069.det = 0 ∧ ∀ i, C6069.adjugate i i ≠ 0) := by
  intro h
  have := certificate6069
  rw [h.1] at this
  norm_num at this
def C6070 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6070 : C6070.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6070 : ¬ (C6070.det = 0 ∧ ∀ i, C6070.adjugate i i ≠ 0) := by
  intro h
  have := certificate6070
  rw [h.1] at this
  norm_num at this
def C6071 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6071 : C6071.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6071 : ¬ (C6071.det = 0 ∧ ∀ i, C6071.adjugate i i ≠ 0) := by
  intro h
  have := certificate6071
  rw [h.1] at this
  norm_num at this
def C6072 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6072 : C6072.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6072 : ¬ (C6072.det = 0 ∧ ∀ i, C6072.adjugate i i ≠ 0) := by
  intro h
  have := certificate6072
  rw [h.1] at this
  norm_num at this
def C6073 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate6073 : C6073.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6073 : ¬ (C6073.det = 0 ∧ ∀ i, C6073.adjugate i i ≠ 0) := by
  intro h
  have := certificate6073
  rw [h.1] at this
  norm_num at this
def C6074 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6074 : C6074.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6074 : ¬ (C6074.det = 0 ∧ ∀ i, C6074.adjugate i i ≠ 0) := by
  intro h
  have := certificate6074
  rw [h.1] at this
  norm_num at this
def C6075 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate6075 : C6075.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6075 : ¬ (C6075.det = 0 ∧ ∀ i, C6075.adjugate i i ≠ 0) := by
  intro h
  have := certificate6075
  rw [h.1] at this
  norm_num at this
def C6076 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6076 : C6076.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6076 : ¬ (C6076.det = 0 ∧ ∀ i, C6076.adjugate i i ≠ 0) := by
  intro h
  have := certificate6076
  rw [h.1] at this
  norm_num at this
def C6077 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate6077 : C6077.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6077 : ¬ (C6077.det = 0 ∧ ∀ i, C6077.adjugate i i ≠ 0) := by
  intro h
  have := certificate6077
  rw [h.1] at this
  norm_num at this
def C6078 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6078 : C6078.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6078 : ¬ (C6078.det = 0 ∧ ∀ i, C6078.adjugate i i ≠ 0) := by
  intro h
  have := certificate6078
  rw [h.1] at this
  norm_num at this
def C6079 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate6079 : C6079.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6079 : ¬ (C6079.det = 0 ∧ ∀ i, C6079.adjugate i i ≠ 0) := by
  intro h
  have := certificate6079
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0189
