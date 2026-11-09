import VerifiedDet
namespace Nut8.NewCertificates0118
def C3776 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate3776 : C3776.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3776 : ¬ (C3776.det = 0 ∧ ∀ i, C3776.adjugate i i ≠ 0) := by
  intro h
  have := certificate3776
  rw [h.1] at this
  norm_num at this
def C3777 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate3777 : C3777.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3777 : ¬ (C3777.det = 0 ∧ ∀ i, C3777.adjugate i i ≠ 0) := by
  intro h
  have := certificate3777
  rw [h.1] at this
  norm_num at this
def C3778 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate3778 : C3778.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3778 : ¬ (C3778.det = 0 ∧ ∀ i, C3778.adjugate i i ≠ 0) := by
  intro h
  have := certificate3778
  rw [h.1] at this
  norm_num at this
def C3779 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate3779 : C3779.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3779 : ¬ (C3779.det = 0 ∧ ∀ i, C3779.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3779
def C3780 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate3780 : C3780.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3780 : ¬ (C3780.det = 0 ∧ ∀ i, C3780.adjugate i i ≠ 0) := by
  intro h
  have := certificate3780
  rw [h.1] at this
  norm_num at this
def C3781 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate3781 : C3781.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3781 : ¬ (C3781.det = 0 ∧ ∀ i, C3781.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3781
def C3782 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate3782 : C3782.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3782 : ¬ (C3782.det = 0 ∧ ∀ i, C3782.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3782
def C3783 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate3783 : C3783.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3783 : ¬ (C3783.det = 0 ∧ ∀ i, C3783.adjugate i i ≠ 0) := by
  intro h
  have := certificate3783
  rw [h.1] at this
  norm_num at this
def C3784 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate3784 : C3784.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3784 : ¬ (C3784.det = 0 ∧ ∀ i, C3784.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3784
def C3785 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate3785 : C3785.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3785 : ¬ (C3785.det = 0 ∧ ∀ i, C3785.adjugate i i ≠ 0) := by
  intro h
  have := certificate3785
  rw [h.1] at this
  norm_num at this
def C3786 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate3786 : C3786.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3786 : ¬ (C3786.det = 0 ∧ ∀ i, C3786.adjugate i i ≠ 0) := by
  intro h
  have := certificate3786
  rw [h.1] at this
  norm_num at this
def C3787 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate3787 : C3787.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3787 : ¬ (C3787.det = 0 ∧ ∀ i, C3787.adjugate i i ≠ 0) := by
  intro h
  have := certificate3787
  rw [h.1] at this
  norm_num at this
def C3788 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate3788 : C3788.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3788 : ¬ (C3788.det = 0 ∧ ∀ i, C3788.adjugate i i ≠ 0) := by
  intro h
  have := certificate3788
  rw [h.1] at this
  norm_num at this
def C3789 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate3789 : C3789.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3789 : ¬ (C3789.det = 0 ∧ ∀ i, C3789.adjugate i i ≠ 0) := by
  intro h
  have := certificate3789
  rw [h.1] at this
  norm_num at this
def C3790 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate3790 : C3790.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3790 : ¬ (C3790.det = 0 ∧ ∀ i, C3790.adjugate i i ≠ 0) := by
  intro h
  have := certificate3790
  rw [h.1] at this
  norm_num at this
def C3791 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate3791 : C3791.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3791 : ¬ (C3791.det = 0 ∧ ∀ i, C3791.adjugate i i ≠ 0) := by
  intro h
  have := certificate3791
  rw [h.1] at this
  norm_num at this
def C3792 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate3792 : C3792.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3792 : ¬ (C3792.det = 0 ∧ ∀ i, C3792.adjugate i i ≠ 0) := by
  intro h
  have := certificate3792
  rw [h.1] at this
  norm_num at this
def C3793 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate3793 : C3793.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3793 : ¬ (C3793.det = 0 ∧ ∀ i, C3793.adjugate i i ≠ 0) := by
  intro h
  have := certificate3793
  rw [h.1] at this
  norm_num at this
def C3794 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate3794 : C3794.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3794 : ¬ (C3794.det = 0 ∧ ∀ i, C3794.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3794
def C3795 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate3795 : C3795.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3795 : ¬ (C3795.det = 0 ∧ ∀ i, C3795.adjugate i i ≠ 0) := by
  intro h
  have := certificate3795
  rw [h.1] at this
  norm_num at this
def C3796 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate3796 : C3796.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction3796 : ¬ (C3796.det = 0 ∧ ∀ i, C3796.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate3796
def C3797 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate3797 : C3797.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3797 : ¬ (C3797.det = 0 ∧ ∀ i, C3797.adjugate i i ≠ 0) := by
  intro h
  have := certificate3797
  rw [h.1] at this
  norm_num at this
def C3798 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3798 : C3798.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3798 : ¬ (C3798.det = 0 ∧ ∀ i, C3798.adjugate i i ≠ 0) := by
  intro h
  have := certificate3798
  rw [h.1] at this
  norm_num at this
def C3799 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3799 : C3799.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3799 : ¬ (C3799.det = 0 ∧ ∀ i, C3799.adjugate i i ≠ 0) := by
  intro h
  have := certificate3799
  rw [h.1] at this
  norm_num at this
def C3800 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3800 : C3800.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3800 : ¬ (C3800.det = 0 ∧ ∀ i, C3800.adjugate i i ≠ 0) := by
  intro h
  have := certificate3800
  rw [h.1] at this
  norm_num at this
def C3801 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3801 : C3801.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3801 : ¬ (C3801.det = 0 ∧ ∀ i, C3801.adjugate i i ≠ 0) := by
  intro h
  have := certificate3801
  rw [h.1] at this
  norm_num at this
def C3802 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3802 : C3802.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3802 : ¬ (C3802.det = 0 ∧ ∀ i, C3802.adjugate i i ≠ 0) := by
  intro h
  have := certificate3802
  rw [h.1] at this
  norm_num at this
def C3803 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3803 : C3803.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3803 : ¬ (C3803.det = 0 ∧ ∀ i, C3803.adjugate i i ≠ 0) := by
  intro h
  have := certificate3803
  rw [h.1] at this
  norm_num at this
def C3804 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3804 : C3804.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3804 : ¬ (C3804.det = 0 ∧ ∀ i, C3804.adjugate i i ≠ 0) := by
  intro h
  have := certificate3804
  rw [h.1] at this
  norm_num at this
def C3805 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3805 : C3805.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3805 : ¬ (C3805.det = 0 ∧ ∀ i, C3805.adjugate i i ≠ 0) := by
  intro h
  have := certificate3805
  rw [h.1] at this
  norm_num at this
def C3806 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3806 : C3806.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3806 : ¬ (C3806.det = 0 ∧ ∀ i, C3806.adjugate i i ≠ 0) := by
  intro h
  have := certificate3806
  rw [h.1] at this
  norm_num at this
def C3807 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3807 : C3807.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3807 : ¬ (C3807.det = 0 ∧ ∀ i, C3807.adjugate i i ≠ 0) := by
  intro h
  have := certificate3807
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0118
