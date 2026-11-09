import VerifiedDet
namespace Nut8.NewCertificates0178
def C5696 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5696 : C5696.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5696 : ¬ (C5696.det = 0 ∧ ∀ i, C5696.adjugate i i ≠ 0) := by
  intro h
  have := certificate5696
  rw [h.1] at this
  norm_num at this
def C5697 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5697 : C5697.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5697 : ¬ (C5697.det = 0 ∧ ∀ i, C5697.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5697
def C5698 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5698 : C5698.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5698 : ¬ (C5698.det = 0 ∧ ∀ i, C5698.adjugate i i ≠ 0) := by
  intro h
  have := certificate5698
  rw [h.1] at this
  norm_num at this
def C5699 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5699 : C5699.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5699 : ¬ (C5699.det = 0 ∧ ∀ i, C5699.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5699
def C5700 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5700 : C5700.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5700 : ¬ (C5700.det = 0 ∧ ∀ i, C5700.adjugate i i ≠ 0) := by
  intro h
  have := certificate5700
  rw [h.1] at this
  norm_num at this
def C5701 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5701 : C5701.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5701 : ¬ (C5701.det = 0 ∧ ∀ i, C5701.adjugate i i ≠ 0) := by
  intro h
  have := certificate5701
  rw [h.1] at this
  norm_num at this
def C5702 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5702 : C5702.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5702 : ¬ (C5702.det = 0 ∧ ∀ i, C5702.adjugate i i ≠ 0) := by
  intro h
  have := certificate5702
  rw [h.1] at this
  norm_num at this
def C5703 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5703 : C5703.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5703 : ¬ (C5703.det = 0 ∧ ∀ i, C5703.adjugate i i ≠ 0) := by
  intro h
  have := certificate5703
  rw [h.1] at this
  norm_num at this
def C5704 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5704 : C5704.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5704 : ¬ (C5704.det = 0 ∧ ∀ i, C5704.adjugate i i ≠ 0) := by
  intro h
  have := certificate5704
  rw [h.1] at this
  norm_num at this
def C5705 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5705 : C5705.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5705 : ¬ (C5705.det = 0 ∧ ∀ i, C5705.adjugate i i ≠ 0) := by
  intro h
  have := certificate5705
  rw [h.1] at this
  norm_num at this
def C5706 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5706 : C5706.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5706 : ¬ (C5706.det = 0 ∧ ∀ i, C5706.adjugate i i ≠ 0) := by
  intro h
  have := certificate5706
  rw [h.1] at this
  norm_num at this
def C5707 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5707 : C5707.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5707 : ¬ (C5707.det = 0 ∧ ∀ i, C5707.adjugate i i ≠ 0) := by
  intro h
  have := certificate5707
  rw [h.1] at this
  norm_num at this
def C5708 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5708 : C5708.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5708 : ¬ (C5708.det = 0 ∧ ∀ i, C5708.adjugate i i ≠ 0) := by
  intro h
  have := certificate5708
  rw [h.1] at this
  norm_num at this
def C5709 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5709 : C5709.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5709 : ¬ (C5709.det = 0 ∧ ∀ i, C5709.adjugate i i ≠ 0) := by
  intro h
  have := certificate5709
  rw [h.1] at this
  norm_num at this
def C5710 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5710 : C5710.det = (88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5710 : ¬ (C5710.det = 0 ∧ ∀ i, C5710.adjugate i i ≠ 0) := by
  intro h
  have := certificate5710
  rw [h.1] at this
  norm_num at this
def C5711 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5711 : C5711.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5711 : ¬ (C5711.det = 0 ∧ ∀ i, C5711.adjugate i i ≠ 0) := by
  intro h
  have := certificate5711
  rw [h.1] at this
  norm_num at this
def C5712 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5712 : C5712.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5712 : ¬ (C5712.det = 0 ∧ ∀ i, C5712.adjugate i i ≠ 0) := by
  intro h
  have := certificate5712
  rw [h.1] at this
  norm_num at this
def C5713 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5713 : C5713.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5713 : ¬ (C5713.det = 0 ∧ ∀ i, C5713.adjugate i i ≠ 0) := by
  intro h
  have := certificate5713
  rw [h.1] at this
  norm_num at this
def C5714 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5714 : C5714.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5714 : ¬ (C5714.det = 0 ∧ ∀ i, C5714.adjugate i i ≠ 0) := by
  intro h
  have := certificate5714
  rw [h.1] at this
  norm_num at this
def C5715 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5715 : C5715.det = (88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5715 : ¬ (C5715.det = 0 ∧ ∀ i, C5715.adjugate i i ≠ 0) := by
  intro h
  have := certificate5715
  rw [h.1] at this
  norm_num at this
def C5716 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5716 : C5716.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5716 : ¬ (C5716.det = 0 ∧ ∀ i, C5716.adjugate i i ≠ 0) := by
  intro h
  have := certificate5716
  rw [h.1] at this
  norm_num at this
def C5717 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5717 : C5717.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5717 : ¬ (C5717.det = 0 ∧ ∀ i, C5717.adjugate i i ≠ 0) := by
  intro h
  have := certificate5717
  rw [h.1] at this
  norm_num at this
def C5718 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5718 : C5718.det = (88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5718 : ¬ (C5718.det = 0 ∧ ∀ i, C5718.adjugate i i ≠ 0) := by
  intro h
  have := certificate5718
  rw [h.1] at this
  norm_num at this
def C5719 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5719 : C5719.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5719 : ¬ (C5719.det = 0 ∧ ∀ i, C5719.adjugate i i ≠ 0) := by
  intro h
  have := certificate5719
  rw [h.1] at this
  norm_num at this
def C5720 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5720 : C5720.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5720 : ¬ (C5720.det = 0 ∧ ∀ i, C5720.adjugate i i ≠ 0) := by
  intro h
  have := certificate5720
  rw [h.1] at this
  norm_num at this
def C5721 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5721 : C5721.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5721 : ¬ (C5721.det = 0 ∧ ∀ i, C5721.adjugate i i ≠ 0) := by
  intro h
  have := certificate5721
  rw [h.1] at this
  norm_num at this
def C5722 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5722 : C5722.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5722 : ¬ (C5722.det = 0 ∧ ∀ i, C5722.adjugate i i ≠ 0) := by
  intro h
  have := certificate5722
  rw [h.1] at this
  norm_num at this
def C5723 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, -2, 0, 0, 0; 0, 1, 0, -2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5723 : C5723.det = (88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5723 : ¬ (C5723.det = 0 ∧ ∀ i, C5723.adjugate i i ≠ 0) := by
  intro h
  have := certificate5723
  rw [h.1] at this
  norm_num at this
def C5724 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1]
theorem certificate5724 : C5724.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5724 : ¬ (C5724.det = 0 ∧ ∀ i, C5724.adjugate i i ≠ 0) := by
  intro h
  have := certificate5724
  rw [h.1] at this
  norm_num at this
def C5725 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, -1]
theorem certificate5725 : C5725.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5725 : ¬ (C5725.det = 0 ∧ ∀ i, C5725.adjugate i i ≠ 0) := by
  intro h
  have := certificate5725
  rw [h.1] at this
  norm_num at this
def C5726 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1]
theorem certificate5726 : C5726.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5726 : ¬ (C5726.det = 0 ∧ ∀ i, C5726.adjugate i i ≠ 0) := by
  intro h
  have := certificate5726
  rw [h.1] at this
  norm_num at this
def C5727 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1]
theorem certificate5727 : C5727.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5727 : ¬ (C5727.det = 0 ∧ ∀ i, C5727.adjugate i i ≠ 0) := by
  intro h
  have := certificate5727
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0178
