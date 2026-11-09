import VerifiedDet
namespace Nut8.NewCertificates0212
def C6784 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6784 : C6784.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6784 : ¬ (C6784.det = 0 ∧ ∀ i, C6784.adjugate i i ≠ 0) := by
  intro h
  have := certificate6784
  rw [h.1] at this
  norm_num at this
def C6785 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6785 : C6785.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6785 : ¬ (C6785.det = 0 ∧ ∀ i, C6785.adjugate i i ≠ 0) := by
  intro h
  have := certificate6785
  rw [h.1] at this
  norm_num at this
def C6786 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6786 : C6786.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6786 : ¬ (C6786.det = 0 ∧ ∀ i, C6786.adjugate i i ≠ 0) := by
  intro h
  have := certificate6786
  rw [h.1] at this
  norm_num at this
def C6787 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6787 : C6787.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6787 : ¬ (C6787.det = 0 ∧ ∀ i, C6787.adjugate i i ≠ 0) := by
  intro h
  have := certificate6787
  rw [h.1] at this
  norm_num at this
def C6788 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6788 : C6788.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6788 : ¬ (C6788.det = 0 ∧ ∀ i, C6788.adjugate i i ≠ 0) := by
  intro h
  have := certificate6788
  rw [h.1] at this
  norm_num at this
def C6789 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6789 : C6789.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6789 : ¬ (C6789.det = 0 ∧ ∀ i, C6789.adjugate i i ≠ 0) := by
  intro h
  have := certificate6789
  rw [h.1] at this
  norm_num at this
def C6790 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6790 : C6790.det = (49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6790 : ¬ (C6790.det = 0 ∧ ∀ i, C6790.adjugate i i ≠ 0) := by
  intro h
  have := certificate6790
  rw [h.1] at this
  norm_num at this
def C6791 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6791 : C6791.det = (49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6791 : ¬ (C6791.det = 0 ∧ ∀ i, C6791.adjugate i i ≠ 0) := by
  intro h
  have := certificate6791
  rw [h.1] at this
  norm_num at this
def C6792 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6792 : C6792.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6792 : ¬ (C6792.det = 0 ∧ ∀ i, C6792.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate6792
def C6793 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6793 : C6793.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6793 : ¬ (C6793.det = 0 ∧ ∀ i, C6793.adjugate i i ≠ 0) := by
  intro h
  have := certificate6793
  rw [h.1] at this
  norm_num at this
def C6794 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6794 : C6794.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6794 : ¬ (C6794.det = 0 ∧ ∀ i, C6794.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate6794
def C6795 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6795 : C6795.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6795 : ¬ (C6795.det = 0 ∧ ∀ i, C6795.adjugate i i ≠ 0) := by
  intro h
  have := certificate6795
  rw [h.1] at this
  norm_num at this
def C6796 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6796 : C6796.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6796 : ¬ (C6796.det = 0 ∧ ∀ i, C6796.adjugate i i ≠ 0) := by
  intro h
  have := certificate6796
  rw [h.1] at this
  norm_num at this
def C6797 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6797 : C6797.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6797 : ¬ (C6797.det = 0 ∧ ∀ i, C6797.adjugate i i ≠ 0) := by
  intro h
  have := certificate6797
  rw [h.1] at this
  norm_num at this
def C6798 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6798 : C6798.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6798 : ¬ (C6798.det = 0 ∧ ∀ i, C6798.adjugate i i ≠ 0) := by
  intro h
  have := certificate6798
  rw [h.1] at this
  norm_num at this
def C6799 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6799 : C6799.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6799 : ¬ (C6799.det = 0 ∧ ∀ i, C6799.adjugate i i ≠ 0) := by
  intro h
  have := certificate6799
  rw [h.1] at this
  norm_num at this
def C6800 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6800 : C6800.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6800 : ¬ (C6800.det = 0 ∧ ∀ i, C6800.adjugate i i ≠ 0) := by
  intro h
  have := certificate6800
  rw [h.1] at this
  norm_num at this
def C6801 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6801 : C6801.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6801 : ¬ (C6801.det = 0 ∧ ∀ i, C6801.adjugate i i ≠ 0) := by
  intro h
  have := certificate6801
  rw [h.1] at this
  norm_num at this
def C6802 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6802 : C6802.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6802 : ¬ (C6802.det = 0 ∧ ∀ i, C6802.adjugate i i ≠ 0) := by
  intro h
  have := certificate6802
  rw [h.1] at this
  norm_num at this
def C6803 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6803 : C6803.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6803 : ¬ (C6803.det = 0 ∧ ∀ i, C6803.adjugate i i ≠ 0) := by
  intro h
  have := certificate6803
  rw [h.1] at this
  norm_num at this
def C6804 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6804 : C6804.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6804 : ¬ (C6804.det = 0 ∧ ∀ i, C6804.adjugate i i ≠ 0) := by
  intro h
  have := certificate6804
  rw [h.1] at this
  norm_num at this
def C6805 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6805 : C6805.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6805 : ¬ (C6805.det = 0 ∧ ∀ i, C6805.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate6805
def C6806 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6806 : C6806.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6806 : ¬ (C6806.det = 0 ∧ ∀ i, C6806.adjugate i i ≠ 0) := by
  intro h
  have := certificate6806
  rw [h.1] at this
  norm_num at this
def C6807 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6807 : C6807.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6807 : ¬ (C6807.det = 0 ∧ ∀ i, C6807.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate6807
def C6808 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6808 : C6808.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6808 : ¬ (C6808.det = 0 ∧ ∀ i, C6808.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate6808
def C6809 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6809 : C6809.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6809 : ¬ (C6809.det = 0 ∧ ∀ i, C6809.adjugate i i ≠ 0) := by
  intro h
  have := certificate6809
  rw [h.1] at this
  norm_num at this
def C6810 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6810 : C6810.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6810 : ¬ (C6810.det = 0 ∧ ∀ i, C6810.adjugate i i ≠ 0) := by
  intro h
  have := certificate6810
  rw [h.1] at this
  norm_num at this
def C6811 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6811 : C6811.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6811 : ¬ (C6811.det = 0 ∧ ∀ i, C6811.adjugate i i ≠ 0) := by
  intro h
  have := certificate6811
  rw [h.1] at this
  norm_num at this
def C6812 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6812 : C6812.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6812 : ¬ (C6812.det = 0 ∧ ∀ i, C6812.adjugate i i ≠ 0) := by
  intro h
  have := certificate6812
  rw [h.1] at this
  norm_num at this
def C6813 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6813 : C6813.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6813 : ¬ (C6813.det = 0 ∧ ∀ i, C6813.adjugate i i ≠ 0) := by
  intro h
  have := certificate6813
  rw [h.1] at this
  norm_num at this
def C6814 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6814 : C6814.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6814 : ¬ (C6814.det = 0 ∧ ∀ i, C6814.adjugate i i ≠ 0) := by
  intro h
  have := certificate6814
  rw [h.1] at this
  norm_num at this
def C6815 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6815 : C6815.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6815 : ¬ (C6815.det = 0 ∧ ∀ i, C6815.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate6815
end Nut8.NewCertificates0212
