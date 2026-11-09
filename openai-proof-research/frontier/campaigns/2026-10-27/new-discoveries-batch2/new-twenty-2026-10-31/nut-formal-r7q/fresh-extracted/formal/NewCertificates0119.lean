import VerifiedDet
namespace Nut8.NewCertificates0119
def C3808 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3808 : C3808.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3808 : ¬ (C3808.det = 0 ∧ ∀ i, C3808.adjugate i i ≠ 0) := by
  intro h
  have := certificate3808
  rw [h.1] at this
  norm_num at this
def C3809 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3809 : C3809.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3809 : ¬ (C3809.det = 0 ∧ ∀ i, C3809.adjugate i i ≠ 0) := by
  intro h
  have := certificate3809
  rw [h.1] at this
  norm_num at this
def C3810 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3810 : C3810.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3810 : ¬ (C3810.det = 0 ∧ ∀ i, C3810.adjugate i i ≠ 0) := by
  intro h
  have := certificate3810
  rw [h.1] at this
  norm_num at this
def C3811 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3811 : C3811.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3811 : ¬ (C3811.det = 0 ∧ ∀ i, C3811.adjugate i i ≠ 0) := by
  intro h
  have := certificate3811
  rw [h.1] at this
  norm_num at this
def C3812 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3812 : C3812.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3812 : ¬ (C3812.det = 0 ∧ ∀ i, C3812.adjugate i i ≠ 0) := by
  intro h
  have := certificate3812
  rw [h.1] at this
  norm_num at this
def C3813 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3813 : C3813.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3813 : ¬ (C3813.det = 0 ∧ ∀ i, C3813.adjugate i i ≠ 0) := by
  intro h
  have := certificate3813
  rw [h.1] at this
  norm_num at this
def C3814 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3814 : C3814.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3814 : ¬ (C3814.det = 0 ∧ ∀ i, C3814.adjugate i i ≠ 0) := by
  intro h
  have := certificate3814
  rw [h.1] at this
  norm_num at this
def C3815 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3815 : C3815.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3815 : ¬ (C3815.det = 0 ∧ ∀ i, C3815.adjugate i i ≠ 0) := by
  intro h
  have := certificate3815
  rw [h.1] at this
  norm_num at this
def C3816 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3816 : C3816.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3816 : ¬ (C3816.det = 0 ∧ ∀ i, C3816.adjugate i i ≠ 0) := by
  intro h
  have := certificate3816
  rw [h.1] at this
  norm_num at this
def C3817 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3817 : C3817.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3817 : ¬ (C3817.det = 0 ∧ ∀ i, C3817.adjugate i i ≠ 0) := by
  intro h
  have := certificate3817
  rw [h.1] at this
  norm_num at this
def C3818 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3818 : C3818.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3818 : ¬ (C3818.det = 0 ∧ ∀ i, C3818.adjugate i i ≠ 0) := by
  intro h
  have := certificate3818
  rw [h.1] at this
  norm_num at this
def C3819 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3819 : C3819.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3819 : ¬ (C3819.det = 0 ∧ ∀ i, C3819.adjugate i i ≠ 0) := by
  intro h
  have := certificate3819
  rw [h.1] at this
  norm_num at this
def C3820 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3820 : C3820.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3820 : ¬ (C3820.det = 0 ∧ ∀ i, C3820.adjugate i i ≠ 0) := by
  intro h
  have := certificate3820
  rw [h.1] at this
  norm_num at this
def C3821 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3821 : C3821.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3821 : ¬ (C3821.det = 0 ∧ ∀ i, C3821.adjugate i i ≠ 0) := by
  intro h
  have := certificate3821
  rw [h.1] at this
  norm_num at this
def C3822 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3822 : C3822.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3822 : ¬ (C3822.det = 0 ∧ ∀ i, C3822.adjugate i i ≠ 0) := by
  intro h
  have := certificate3822
  rw [h.1] at this
  norm_num at this
def C3823 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3823 : C3823.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3823 : ¬ (C3823.det = 0 ∧ ∀ i, C3823.adjugate i i ≠ 0) := by
  intro h
  have := certificate3823
  rw [h.1] at this
  norm_num at this
def C3824 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3824 : C3824.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3824 : ¬ (C3824.det = 0 ∧ ∀ i, C3824.adjugate i i ≠ 0) := by
  intro h
  have := certificate3824
  rw [h.1] at this
  norm_num at this
def C3825 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3825 : C3825.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3825 : ¬ (C3825.det = 0 ∧ ∀ i, C3825.adjugate i i ≠ 0) := by
  intro h
  have := certificate3825
  rw [h.1] at this
  norm_num at this
def C3826 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3826 : C3826.det = (-27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3826 : ¬ (C3826.det = 0 ∧ ∀ i, C3826.adjugate i i ≠ 0) := by
  intro h
  have := certificate3826
  rw [h.1] at this
  norm_num at this
def C3827 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3827 : C3827.det = (45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3827 : ¬ (C3827.det = 0 ∧ ∀ i, C3827.adjugate i i ≠ 0) := by
  intro h
  have := certificate3827
  rw [h.1] at this
  norm_num at this
def C3828 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3828 : C3828.det = (45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3828 : ¬ (C3828.det = 0 ∧ ∀ i, C3828.adjugate i i ≠ 0) := by
  intro h
  have := certificate3828
  rw [h.1] at this
  norm_num at this
def C3829 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3829 : C3829.det = (-27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3829 : ¬ (C3829.det = 0 ∧ ∀ i, C3829.adjugate i i ≠ 0) := by
  intro h
  have := certificate3829
  rw [h.1] at this
  norm_num at this
def C3830 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3830 : C3830.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3830 : ¬ (C3830.det = 0 ∧ ∀ i, C3830.adjugate i i ≠ 0) := by
  intro h
  have := certificate3830
  rw [h.1] at this
  norm_num at this
def C3831 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3831 : C3831.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3831 : ¬ (C3831.det = 0 ∧ ∀ i, C3831.adjugate i i ≠ 0) := by
  intro h
  have := certificate3831
  rw [h.1] at this
  norm_num at this
def C3832 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3832 : C3832.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3832 : ¬ (C3832.det = 0 ∧ ∀ i, C3832.adjugate i i ≠ 0) := by
  intro h
  have := certificate3832
  rw [h.1] at this
  norm_num at this
def C3833 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3833 : C3833.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3833 : ¬ (C3833.det = 0 ∧ ∀ i, C3833.adjugate i i ≠ 0) := by
  intro h
  have := certificate3833
  rw [h.1] at this
  norm_num at this
def C3834 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3834 : C3834.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3834 : ¬ (C3834.det = 0 ∧ ∀ i, C3834.adjugate i i ≠ 0) := by
  intro h
  have := certificate3834
  rw [h.1] at this
  norm_num at this
def C3835 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3835 : C3835.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3835 : ¬ (C3835.det = 0 ∧ ∀ i, C3835.adjugate i i ≠ 0) := by
  intro h
  have := certificate3835
  rw [h.1] at this
  norm_num at this
def C3836 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3836 : C3836.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3836 : ¬ (C3836.det = 0 ∧ ∀ i, C3836.adjugate i i ≠ 0) := by
  intro h
  have := certificate3836
  rw [h.1] at this
  norm_num at this
def C3837 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3837 : C3837.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3837 : ¬ (C3837.det = 0 ∧ ∀ i, C3837.adjugate i i ≠ 0) := by
  intro h
  have := certificate3837
  rw [h.1] at this
  norm_num at this
def C3838 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3838 : C3838.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3838 : ¬ (C3838.det = 0 ∧ ∀ i, C3838.adjugate i i ≠ 0) := by
  intro h
  have := certificate3838
  rw [h.1] at this
  norm_num at this
def C3839 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3839 : C3839.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3839 : ¬ (C3839.det = 0 ∧ ∀ i, C3839.adjugate i i ≠ 0) := by
  intro h
  have := certificate3839
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0119
