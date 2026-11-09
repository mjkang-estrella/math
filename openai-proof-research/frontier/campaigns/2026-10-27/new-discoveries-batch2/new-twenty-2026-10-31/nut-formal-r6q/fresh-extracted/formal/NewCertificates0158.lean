import VerifiedDet
namespace Nut8.NewCertificates0158
def C5056 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5056 : C5056.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5056 : ¬ (C5056.det = 0 ∧ ∀ i, C5056.adjugate i i ≠ 0) := by
  intro h
  have := certificate5056
  rw [h.1] at this
  norm_num at this
def C5057 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5057 : C5057.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5057 : ¬ (C5057.det = 0 ∧ ∀ i, C5057.adjugate i i ≠ 0) := by
  intro h
  have := certificate5057
  rw [h.1] at this
  norm_num at this
def C5058 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5058 : C5058.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5058 : ¬ (C5058.det = 0 ∧ ∀ i, C5058.adjugate i i ≠ 0) := by
  intro h
  have := certificate5058
  rw [h.1] at this
  norm_num at this
def C5059 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5059 : C5059.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5059 : ¬ (C5059.det = 0 ∧ ∀ i, C5059.adjugate i i ≠ 0) := by
  intro h
  have := certificate5059
  rw [h.1] at this
  norm_num at this
def C5060 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5060 : C5060.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5060 : ¬ (C5060.det = 0 ∧ ∀ i, C5060.adjugate i i ≠ 0) := by
  intro h
  have := certificate5060
  rw [h.1] at this
  norm_num at this
def C5061 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5061 : C5061.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5061 : ¬ (C5061.det = 0 ∧ ∀ i, C5061.adjugate i i ≠ 0) := by
  intro h
  have := certificate5061
  rw [h.1] at this
  norm_num at this
def C5062 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5062 : C5062.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5062 : ¬ (C5062.det = 0 ∧ ∀ i, C5062.adjugate i i ≠ 0) := by
  intro h
  have := certificate5062
  rw [h.1] at this
  norm_num at this
def C5063 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5063 : C5063.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5063 : ¬ (C5063.det = 0 ∧ ∀ i, C5063.adjugate i i ≠ 0) := by
  intro h
  have := certificate5063
  rw [h.1] at this
  norm_num at this
def C5064 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5064 : C5064.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5064 : ¬ (C5064.det = 0 ∧ ∀ i, C5064.adjugate i i ≠ 0) := by
  intro h
  have := certificate5064
  rw [h.1] at this
  norm_num at this
def C5065 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5065 : C5065.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5065 : ¬ (C5065.det = 0 ∧ ∀ i, C5065.adjugate i i ≠ 0) := by
  intro h
  have := certificate5065
  rw [h.1] at this
  norm_num at this
def C5066 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5066 : C5066.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5066 : ¬ (C5066.det = 0 ∧ ∀ i, C5066.adjugate i i ≠ 0) := by
  intro h
  have := certificate5066
  rw [h.1] at this
  norm_num at this
def C5067 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5067 : C5067.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5067 : ¬ (C5067.det = 0 ∧ ∀ i, C5067.adjugate i i ≠ 0) := by
  intro h
  have := certificate5067
  rw [h.1] at this
  norm_num at this
def C5068 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5068 : C5068.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5068 : ¬ (C5068.det = 0 ∧ ∀ i, C5068.adjugate i i ≠ 0) := by
  intro h
  have := certificate5068
  rw [h.1] at this
  norm_num at this
def C5069 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5069 : C5069.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5069 : ¬ (C5069.det = 0 ∧ ∀ i, C5069.adjugate i i ≠ 0) := by
  intro h
  have := certificate5069
  rw [h.1] at this
  norm_num at this
def C5070 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5070 : C5070.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5070 : ¬ (C5070.det = 0 ∧ ∀ i, C5070.adjugate i i ≠ 0) := by
  intro h
  have := certificate5070
  rw [h.1] at this
  norm_num at this
def C5071 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5071 : C5071.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5071 : ¬ (C5071.det = 0 ∧ ∀ i, C5071.adjugate i i ≠ 0) := by
  intro h
  have := certificate5071
  rw [h.1] at this
  norm_num at this
def C5072 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5072 : C5072.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5072 : ¬ (C5072.det = 0 ∧ ∀ i, C5072.adjugate i i ≠ 0) := by
  intro h
  have := certificate5072
  rw [h.1] at this
  norm_num at this
def C5073 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5073 : C5073.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5073 : ¬ (C5073.det = 0 ∧ ∀ i, C5073.adjugate i i ≠ 0) := by
  intro h
  have := certificate5073
  rw [h.1] at this
  norm_num at this
def C5074 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5074 : C5074.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5074 : ¬ (C5074.det = 0 ∧ ∀ i, C5074.adjugate i i ≠ 0) := by
  intro h
  have := certificate5074
  rw [h.1] at this
  norm_num at this
def C5075 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5075 : C5075.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5075 : ¬ (C5075.det = 0 ∧ ∀ i, C5075.adjugate i i ≠ 0) := by
  intro h
  have := certificate5075
  rw [h.1] at this
  norm_num at this
def C5076 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5076 : C5076.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5076 : ¬ (C5076.det = 0 ∧ ∀ i, C5076.adjugate i i ≠ 0) := by
  intro h
  have := certificate5076
  rw [h.1] at this
  norm_num at this
def C5077 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5077 : C5077.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5077 : ¬ (C5077.det = 0 ∧ ∀ i, C5077.adjugate i i ≠ 0) := by
  intro h
  have := certificate5077
  rw [h.1] at this
  norm_num at this
def C5078 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5078 : C5078.det = (-99 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5078 : ¬ (C5078.det = 0 ∧ ∀ i, C5078.adjugate i i ≠ 0) := by
  intro h
  have := certificate5078
  rw [h.1] at this
  norm_num at this
def C5079 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5079 : C5079.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5079 : ¬ (C5079.det = 0 ∧ ∀ i, C5079.adjugate i i ≠ 0) := by
  intro h
  have := certificate5079
  rw [h.1] at this
  norm_num at this
def C5080 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5080 : C5080.det = (93 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5080 : ¬ (C5080.det = 0 ∧ ∀ i, C5080.adjugate i i ≠ 0) := by
  intro h
  have := certificate5080
  rw [h.1] at this
  norm_num at this
def C5081 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5081 : C5081.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5081 : ¬ (C5081.det = 0 ∧ ∀ i, C5081.adjugate i i ≠ 0) := by
  intro h
  have := certificate5081
  rw [h.1] at this
  norm_num at this
def C5082 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5082 : C5082.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5082 : ¬ (C5082.det = 0 ∧ ∀ i, C5082.adjugate i i ≠ 0) := by
  intro h
  have := certificate5082
  rw [h.1] at this
  norm_num at this
def C5083 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5083 : C5083.det = (93 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5083 : ¬ (C5083.det = 0 ∧ ∀ i, C5083.adjugate i i ≠ 0) := by
  intro h
  have := certificate5083
  rw [h.1] at this
  norm_num at this
def C5084 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5084 : C5084.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5084 : ¬ (C5084.det = 0 ∧ ∀ i, C5084.adjugate i i ≠ 0) := by
  intro h
  have := certificate5084
  rw [h.1] at this
  norm_num at this
def C5085 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5085 : C5085.det = (-99 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5085 : ¬ (C5085.det = 0 ∧ ∀ i, C5085.adjugate i i ≠ 0) := by
  intro h
  have := certificate5085
  rw [h.1] at this
  norm_num at this
def C5086 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5086 : C5086.det = (-72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5086 : ¬ (C5086.det = 0 ∧ ∀ i, C5086.adjugate i i ≠ 0) := by
  intro h
  have := certificate5086
  rw [h.1] at this
  norm_num at this
def C5087 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5087 : C5087.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5087 : ¬ (C5087.det = 0 ∧ ∀ i, C5087.adjugate i i ≠ 0) := by
  intro h
  have := certificate5087
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0158
