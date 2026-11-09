import VerifiedDet
namespace Nut8.NewCertificates0181
def C5792 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5792 : C5792.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5792 : ¬ (C5792.det = 0 ∧ ∀ i, C5792.adjugate i i ≠ 0) := by
  intro h
  have := certificate5792
  rw [h.1] at this
  norm_num at this
def C5793 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5793 : C5793.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5793 : ¬ (C5793.det = 0 ∧ ∀ i, C5793.adjugate i i ≠ 0) := by
  intro h
  have := certificate5793
  rw [h.1] at this
  norm_num at this
def C5794 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5794 : C5794.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5794 : ¬ (C5794.det = 0 ∧ ∀ i, C5794.adjugate i i ≠ 0) := by
  intro h
  have := certificate5794
  rw [h.1] at this
  norm_num at this
def C5795 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5795 : C5795.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5795 : ¬ (C5795.det = 0 ∧ ∀ i, C5795.adjugate i i ≠ 0) := by
  intro h
  have := certificate5795
  rw [h.1] at this
  norm_num at this
def C5796 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5796 : C5796.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5796 : ¬ (C5796.det = 0 ∧ ∀ i, C5796.adjugate i i ≠ 0) := by
  intro h
  have := certificate5796
  rw [h.1] at this
  norm_num at this
def C5797 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5797 : C5797.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5797 : ¬ (C5797.det = 0 ∧ ∀ i, C5797.adjugate i i ≠ 0) := by
  intro h
  have := certificate5797
  rw [h.1] at this
  norm_num at this
def C5798 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5798 : C5798.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5798 : ¬ (C5798.det = 0 ∧ ∀ i, C5798.adjugate i i ≠ 0) := by
  intro h
  have := certificate5798
  rw [h.1] at this
  norm_num at this
def C5799 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5799 : C5799.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5799 : ¬ (C5799.det = 0 ∧ ∀ i, C5799.adjugate i i ≠ 0) := by
  intro h
  have := certificate5799
  rw [h.1] at this
  norm_num at this
def C5800 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5800 : C5800.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5800 : ¬ (C5800.det = 0 ∧ ∀ i, C5800.adjugate i i ≠ 0) := by
  intro h
  have := certificate5800
  rw [h.1] at this
  norm_num at this
def C5801 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5801 : C5801.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5801 : ¬ (C5801.det = 0 ∧ ∀ i, C5801.adjugate i i ≠ 0) := by
  intro h
  have := certificate5801
  rw [h.1] at this
  norm_num at this
def C5802 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5802 : C5802.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5802 : ¬ (C5802.det = 0 ∧ ∀ i, C5802.adjugate i i ≠ 0) := by
  intro h
  have := certificate5802
  rw [h.1] at this
  norm_num at this
def C5803 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5803 : C5803.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5803 : ¬ (C5803.det = 0 ∧ ∀ i, C5803.adjugate i i ≠ 0) := by
  intro h
  have := certificate5803
  rw [h.1] at this
  norm_num at this
def C5804 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5804 : C5804.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5804 : ¬ (C5804.det = 0 ∧ ∀ i, C5804.adjugate i i ≠ 0) := by
  intro h
  have := certificate5804
  rw [h.1] at this
  norm_num at this
def C5805 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5805 : C5805.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5805 : ¬ (C5805.det = 0 ∧ ∀ i, C5805.adjugate i i ≠ 0) := by
  intro h
  have := certificate5805
  rw [h.1] at this
  norm_num at this
def C5806 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5806 : C5806.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5806 : ¬ (C5806.det = 0 ∧ ∀ i, C5806.adjugate i i ≠ 0) := by
  intro h
  have := certificate5806
  rw [h.1] at this
  norm_num at this
def C5807 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5807 : C5807.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5807 : ¬ (C5807.det = 0 ∧ ∀ i, C5807.adjugate i i ≠ 0) := by
  intro h
  have := certificate5807
  rw [h.1] at this
  norm_num at this
def C5808 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5808 : C5808.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5808 : ¬ (C5808.det = 0 ∧ ∀ i, C5808.adjugate i i ≠ 0) := by
  intro h
  have := certificate5808
  rw [h.1] at this
  norm_num at this
def C5809 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5809 : C5809.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5809 : ¬ (C5809.det = 0 ∧ ∀ i, C5809.adjugate i i ≠ 0) := by
  intro h
  have := certificate5809
  rw [h.1] at this
  norm_num at this
def C5810 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5810 : C5810.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5810 : ¬ (C5810.det = 0 ∧ ∀ i, C5810.adjugate i i ≠ 0) := by
  intro h
  have := certificate5810
  rw [h.1] at this
  norm_num at this
def C5811 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5811 : C5811.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5811 : ¬ (C5811.det = 0 ∧ ∀ i, C5811.adjugate i i ≠ 0) := by
  intro h
  have := certificate5811
  rw [h.1] at this
  norm_num at this
def C5812 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5812 : C5812.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5812 : ¬ (C5812.det = 0 ∧ ∀ i, C5812.adjugate i i ≠ 0) := by
  intro h
  have := certificate5812
  rw [h.1] at this
  norm_num at this
def C5813 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5813 : C5813.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5813 : ¬ (C5813.det = 0 ∧ ∀ i, C5813.adjugate i i ≠ 0) := by
  intro h
  have := certificate5813
  rw [h.1] at this
  norm_num at this
def C5814 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5814 : C5814.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5814 : ¬ (C5814.det = 0 ∧ ∀ i, C5814.adjugate i i ≠ 0) := by
  intro h
  have := certificate5814
  rw [h.1] at this
  norm_num at this
def C5815 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5815 : C5815.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5815 : ¬ (C5815.det = 0 ∧ ∀ i, C5815.adjugate i i ≠ 0) := by
  intro h
  have := certificate5815
  rw [h.1] at this
  norm_num at this
def C5816 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5816 : C5816.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5816 : ¬ (C5816.det = 0 ∧ ∀ i, C5816.adjugate i i ≠ 0) := by
  intro h
  have := certificate5816
  rw [h.1] at this
  norm_num at this
def C5817 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5817 : C5817.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5817 : ¬ (C5817.det = 0 ∧ ∀ i, C5817.adjugate i i ≠ 0) := by
  intro h
  have := certificate5817
  rw [h.1] at this
  norm_num at this
def C5818 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5818 : C5818.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5818 : ¬ (C5818.det = 0 ∧ ∀ i, C5818.adjugate i i ≠ 0) := by
  intro h
  have := certificate5818
  rw [h.1] at this
  norm_num at this
def C5819 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5819 : C5819.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5819 : ¬ (C5819.det = 0 ∧ ∀ i, C5819.adjugate i i ≠ 0) := by
  intro h
  have := certificate5819
  rw [h.1] at this
  norm_num at this
def C5820 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5820 : C5820.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5820 : ¬ (C5820.det = 0 ∧ ∀ i, C5820.adjugate i i ≠ 0) := by
  intro h
  have := certificate5820
  rw [h.1] at this
  norm_num at this
def C5821 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5821 : C5821.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5821 : ¬ (C5821.det = 0 ∧ ∀ i, C5821.adjugate i i ≠ 0) := by
  intro h
  have := certificate5821
  rw [h.1] at this
  norm_num at this
def C5822 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5822 : C5822.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5822 : ¬ (C5822.det = 0 ∧ ∀ i, C5822.adjugate i i ≠ 0) := by
  intro h
  have := certificate5822
  rw [h.1] at this
  norm_num at this
def C5823 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5823 : C5823.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5823 : ¬ (C5823.det = 0 ∧ ∀ i, C5823.adjugate i i ≠ 0) := by
  intro h
  have := certificate5823
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0181
