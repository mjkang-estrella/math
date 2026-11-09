import VerifiedDet
namespace Nut8.NewCertificates0275
def C8800 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8800 : C8800.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8800 : ¬ (C8800.det = 0 ∧ ∀ i, C8800.adjugate i i ≠ 0) := by
  intro h
  have := certificate8800
  rw [h.1] at this
  norm_num at this
def C8801 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8801 : C8801.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8801 : ¬ (C8801.det = 0 ∧ ∀ i, C8801.adjugate i i ≠ 0) := by
  intro h
  have := certificate8801
  rw [h.1] at this
  norm_num at this
def C8802 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8802 : C8802.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8802 : ¬ (C8802.det = 0 ∧ ∀ i, C8802.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8802
def C8803 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8803 : C8803.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8803 : ¬ (C8803.det = 0 ∧ ∀ i, C8803.adjugate i i ≠ 0) := by
  intro h
  have := certificate8803
  rw [h.1] at this
  norm_num at this
def C8804 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8804 : C8804.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8804 : ¬ (C8804.det = 0 ∧ ∀ i, C8804.adjugate i i ≠ 0) := by
  intro h
  have := certificate8804
  rw [h.1] at this
  norm_num at this
def C8805 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8805 : C8805.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8805 : ¬ (C8805.det = 0 ∧ ∀ i, C8805.adjugate i i ≠ 0) := by
  intro h
  have := certificate8805
  rw [h.1] at this
  norm_num at this
def C8806 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8806 : C8806.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8806 : ¬ (C8806.det = 0 ∧ ∀ i, C8806.adjugate i i ≠ 0) := by
  intro h
  have := certificate8806
  rw [h.1] at this
  norm_num at this
def C8807 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8807 : C8807.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8807 : ¬ (C8807.det = 0 ∧ ∀ i, C8807.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8807
def C8808 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8808 : C8808.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8808 : ¬ (C8808.det = 0 ∧ ∀ i, C8808.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8808
def C8809 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8809 : C8809.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8809 : ¬ (C8809.det = 0 ∧ ∀ i, C8809.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8809
def C8810 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8810 : C8810.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8810 : ¬ (C8810.det = 0 ∧ ∀ i, C8810.adjugate i i ≠ 0) := by
  intro h
  have := certificate8810
  rw [h.1] at this
  norm_num at this
def C8811 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8811 : C8811.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8811 : ¬ (C8811.det = 0 ∧ ∀ i, C8811.adjugate i i ≠ 0) := by
  intro h
  have := certificate8811
  rw [h.1] at this
  norm_num at this
def C8812 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8812 : C8812.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8812 : ¬ (C8812.det = 0 ∧ ∀ i, C8812.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8812
def C8813 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8813 : C8813.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8813 : ¬ (C8813.det = 0 ∧ ∀ i, C8813.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8813
def C8814 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8814 : C8814.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8814 : ¬ (C8814.det = 0 ∧ ∀ i, C8814.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8814
def C8815 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8815 : C8815.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8815 : ¬ (C8815.det = 0 ∧ ∀ i, C8815.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8815
def C8816 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8816 : C8816.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8816 : ¬ (C8816.det = 0 ∧ ∀ i, C8816.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8816
def C8817 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8817 : C8817.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8817 : ¬ (C8817.det = 0 ∧ ∀ i, C8817.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8817
def C8818 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8818 : C8818.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8818 : ¬ (C8818.det = 0 ∧ ∀ i, C8818.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8818
def C8819 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8819 : C8819.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8819 : ¬ (C8819.det = 0 ∧ ∀ i, C8819.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8819
def C8820 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8820 : C8820.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8820 : ¬ (C8820.det = 0 ∧ ∀ i, C8820.adjugate i i ≠ 0) := by
  intro h
  have := certificate8820
  rw [h.1] at this
  norm_num at this
def C8821 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8821 : C8821.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8821 : ¬ (C8821.det = 0 ∧ ∀ i, C8821.adjugate i i ≠ 0) := by
  intro h
  have := certificate8821
  rw [h.1] at this
  norm_num at this
def C8822 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8822 : C8822.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8822 : ¬ (C8822.det = 0 ∧ ∀ i, C8822.adjugate i i ≠ 0) := by
  intro h
  have := certificate8822
  rw [h.1] at this
  norm_num at this
def C8823 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8823 : C8823.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8823 : ¬ (C8823.det = 0 ∧ ∀ i, C8823.adjugate i i ≠ 0) := by
  intro h
  have := certificate8823
  rw [h.1] at this
  norm_num at this
def C8824 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8824 : C8824.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8824 : ¬ (C8824.det = 0 ∧ ∀ i, C8824.adjugate i i ≠ 0) := by
  intro h
  have := certificate8824
  rw [h.1] at this
  norm_num at this
def C8825 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8825 : C8825.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8825 : ¬ (C8825.det = 0 ∧ ∀ i, C8825.adjugate i i ≠ 0) := by
  intro h
  have := certificate8825
  rw [h.1] at this
  norm_num at this
def C8826 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8826 : C8826.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8826 : ¬ (C8826.det = 0 ∧ ∀ i, C8826.adjugate i i ≠ 0) := by
  intro h
  have := certificate8826
  rw [h.1] at this
  norm_num at this
def C8827 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8827 : C8827.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8827 : ¬ (C8827.det = 0 ∧ ∀ i, C8827.adjugate i i ≠ 0) := by
  intro h
  have := certificate8827
  rw [h.1] at this
  norm_num at this
def C8828 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8828 : C8828.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8828 : ¬ (C8828.det = 0 ∧ ∀ i, C8828.adjugate i i ≠ 0) := by
  intro h
  have := certificate8828
  rw [h.1] at this
  norm_num at this
def C8829 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8829 : C8829.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8829 : ¬ (C8829.det = 0 ∧ ∀ i, C8829.adjugate i i ≠ 0) := by
  intro h
  have := certificate8829
  rw [h.1] at this
  norm_num at this
def C8830 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8830 : C8830.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8830 : ¬ (C8830.det = 0 ∧ ∀ i, C8830.adjugate i i ≠ 0) := by
  intro h
  have := certificate8830
  rw [h.1] at this
  norm_num at this
def C8831 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8831 : C8831.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8831 : ¬ (C8831.det = 0 ∧ ∀ i, C8831.adjugate i i ≠ 0) := by
  intro h
  have := certificate8831
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0275
