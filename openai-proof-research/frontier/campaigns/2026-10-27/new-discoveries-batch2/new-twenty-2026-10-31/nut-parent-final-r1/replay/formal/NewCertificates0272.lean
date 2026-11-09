import VerifiedDet
namespace Nut8.NewCertificates0272
def C8704 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8704 : C8704.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8704 : ¬ (C8704.det = 0 ∧ ∀ i, C8704.adjugate i i ≠ 0) := by
  intro h
  have := certificate8704
  rw [h.1] at this
  norm_num at this
def C8705 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8705 : C8705.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8705 : ¬ (C8705.det = 0 ∧ ∀ i, C8705.adjugate i i ≠ 0) := by
  intro h
  have := certificate8705
  rw [h.1] at this
  norm_num at this
def C8706 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8706 : C8706.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8706 : ¬ (C8706.det = 0 ∧ ∀ i, C8706.adjugate i i ≠ 0) := by
  intro h
  have := certificate8706
  rw [h.1] at this
  norm_num at this
def C8707 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8707 : C8707.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8707 : ¬ (C8707.det = 0 ∧ ∀ i, C8707.adjugate i i ≠ 0) := by
  intro h
  have := certificate8707
  rw [h.1] at this
  norm_num at this
def C8708 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8708 : C8708.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8708 : ¬ (C8708.det = 0 ∧ ∀ i, C8708.adjugate i i ≠ 0) := by
  intro h
  have := certificate8708
  rw [h.1] at this
  norm_num at this
def C8709 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8709 : C8709.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8709 : ¬ (C8709.det = 0 ∧ ∀ i, C8709.adjugate i i ≠ 0) := by
  intro h
  have := certificate8709
  rw [h.1] at this
  norm_num at this
def C8710 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8710 : C8710.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8710 : ¬ (C8710.det = 0 ∧ ∀ i, C8710.adjugate i i ≠ 0) := by
  intro h
  have := certificate8710
  rw [h.1] at this
  norm_num at this
def C8711 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8711 : C8711.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8711 : ¬ (C8711.det = 0 ∧ ∀ i, C8711.adjugate i i ≠ 0) := by
  intro h
  have := certificate8711
  rw [h.1] at this
  norm_num at this
def C8712 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8712 : C8712.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8712 : ¬ (C8712.det = 0 ∧ ∀ i, C8712.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8712
def C8713 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8713 : C8713.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8713 : ¬ (C8713.det = 0 ∧ ∀ i, C8713.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8713
def C8714 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8714 : C8714.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8714 : ¬ (C8714.det = 0 ∧ ∀ i, C8714.adjugate i i ≠ 0) := by
  intro h
  have := certificate8714
  rw [h.1] at this
  norm_num at this
def C8715 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8715 : C8715.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8715 : ¬ (C8715.det = 0 ∧ ∀ i, C8715.adjugate i i ≠ 0) := by
  intro h
  have := certificate8715
  rw [h.1] at this
  norm_num at this
def C8716 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8716 : C8716.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8716 : ¬ (C8716.det = 0 ∧ ∀ i, C8716.adjugate i i ≠ 0) := by
  intro h
  have := certificate8716
  rw [h.1] at this
  norm_num at this
def C8717 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8717 : C8717.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8717 : ¬ (C8717.det = 0 ∧ ∀ i, C8717.adjugate i i ≠ 0) := by
  intro h
  have := certificate8717
  rw [h.1] at this
  norm_num at this
def C8718 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8718 : C8718.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8718 : ¬ (C8718.det = 0 ∧ ∀ i, C8718.adjugate i i ≠ 0) := by
  intro h
  have := certificate8718
  rw [h.1] at this
  norm_num at this
def C8719 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8719 : C8719.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8719 : ¬ (C8719.det = 0 ∧ ∀ i, C8719.adjugate i i ≠ 0) := by
  intro h
  have := certificate8719
  rw [h.1] at this
  norm_num at this
def C8720 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate8720 : C8720.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8720 : ¬ (C8720.det = 0 ∧ ∀ i, C8720.adjugate i i ≠ 0) := by
  intro h
  have := certificate8720
  rw [h.1] at this
  norm_num at this
def C8721 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate8721 : C8721.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8721 : ¬ (C8721.det = 0 ∧ ∀ i, C8721.adjugate i i ≠ 0) := by
  intro h
  have := certificate8721
  rw [h.1] at this
  norm_num at this
def C8722 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate8722 : C8722.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8722 : ¬ (C8722.det = 0 ∧ ∀ i, C8722.adjugate i i ≠ 0) := by
  intro h
  have := certificate8722
  rw [h.1] at this
  norm_num at this
def C8723 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate8723 : C8723.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8723 : ¬ (C8723.det = 0 ∧ ∀ i, C8723.adjugate i i ≠ 0) := by
  intro h
  have := certificate8723
  rw [h.1] at this
  norm_num at this
def C8724 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8724 : C8724.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8724 : ¬ (C8724.det = 0 ∧ ∀ i, C8724.adjugate i i ≠ 0) := by
  intro h
  have := certificate8724
  rw [h.1] at this
  norm_num at this
def C8725 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8725 : C8725.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8725 : ¬ (C8725.det = 0 ∧ ∀ i, C8725.adjugate i i ≠ 0) := by
  intro h
  have := certificate8725
  rw [h.1] at this
  norm_num at this
def C8726 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8726 : C8726.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8726 : ¬ (C8726.det = 0 ∧ ∀ i, C8726.adjugate i i ≠ 0) := by
  intro h
  have := certificate8726
  rw [h.1] at this
  norm_num at this
def C8727 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8727 : C8727.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8727 : ¬ (C8727.det = 0 ∧ ∀ i, C8727.adjugate i i ≠ 0) := by
  intro h
  have := certificate8727
  rw [h.1] at this
  norm_num at this
def C8728 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate8728 : C8728.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8728 : ¬ (C8728.det = 0 ∧ ∀ i, C8728.adjugate i i ≠ 0) := by
  intro h
  have := certificate8728
  rw [h.1] at this
  norm_num at this
def C8729 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate8729 : C8729.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8729 : ¬ (C8729.det = 0 ∧ ∀ i, C8729.adjugate i i ≠ 0) := by
  intro h
  have := certificate8729
  rw [h.1] at this
  norm_num at this
def C8730 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate8730 : C8730.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8730 : ¬ (C8730.det = 0 ∧ ∀ i, C8730.adjugate i i ≠ 0) := by
  intro h
  have := certificate8730
  rw [h.1] at this
  norm_num at this
def C8731 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate8731 : C8731.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8731 : ¬ (C8731.det = 0 ∧ ∀ i, C8731.adjugate i i ≠ 0) := by
  intro h
  have := certificate8731
  rw [h.1] at this
  norm_num at this
def C8732 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8732 : C8732.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8732 : ¬ (C8732.det = 0 ∧ ∀ i, C8732.adjugate i i ≠ 0) := by
  intro h
  have := certificate8732
  rw [h.1] at this
  norm_num at this
def C8733 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8733 : C8733.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8733 : ¬ (C8733.det = 0 ∧ ∀ i, C8733.adjugate i i ≠ 0) := by
  intro h
  have := certificate8733
  rw [h.1] at this
  norm_num at this
def C8734 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8734 : C8734.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8734 : ¬ (C8734.det = 0 ∧ ∀ i, C8734.adjugate i i ≠ 0) := by
  intro h
  have := certificate8734
  rw [h.1] at this
  norm_num at this
def C8735 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8735 : C8735.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8735 : ¬ (C8735.det = 0 ∧ ∀ i, C8735.adjugate i i ≠ 0) := by
  intro h
  have := certificate8735
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0272
