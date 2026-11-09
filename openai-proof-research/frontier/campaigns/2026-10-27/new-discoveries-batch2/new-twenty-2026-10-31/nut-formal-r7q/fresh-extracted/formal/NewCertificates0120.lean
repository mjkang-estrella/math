import VerifiedDet
namespace Nut8.NewCertificates0120
def C3840 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3840 : C3840.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3840 : ¬ (C3840.det = 0 ∧ ∀ i, C3840.adjugate i i ≠ 0) := by
  intro h
  have := certificate3840
  rw [h.1] at this
  norm_num at this
def C3841 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3841 : C3841.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3841 : ¬ (C3841.det = 0 ∧ ∀ i, C3841.adjugate i i ≠ 0) := by
  intro h
  have := certificate3841
  rw [h.1] at this
  norm_num at this
def C3842 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3842 : C3842.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3842 : ¬ (C3842.det = 0 ∧ ∀ i, C3842.adjugate i i ≠ 0) := by
  intro h
  have := certificate3842
  rw [h.1] at this
  norm_num at this
def C3843 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3843 : C3843.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3843 : ¬ (C3843.det = 0 ∧ ∀ i, C3843.adjugate i i ≠ 0) := by
  intro h
  have := certificate3843
  rw [h.1] at this
  norm_num at this
def C3844 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3844 : C3844.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3844 : ¬ (C3844.det = 0 ∧ ∀ i, C3844.adjugate i i ≠ 0) := by
  intro h
  have := certificate3844
  rw [h.1] at this
  norm_num at this
def C3845 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3845 : C3845.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3845 : ¬ (C3845.det = 0 ∧ ∀ i, C3845.adjugate i i ≠ 0) := by
  intro h
  have := certificate3845
  rw [h.1] at this
  norm_num at this
def C3846 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3846 : C3846.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3846 : ¬ (C3846.det = 0 ∧ ∀ i, C3846.adjugate i i ≠ 0) := by
  intro h
  have := certificate3846
  rw [h.1] at this
  norm_num at this
def C3847 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3847 : C3847.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3847 : ¬ (C3847.det = 0 ∧ ∀ i, C3847.adjugate i i ≠ 0) := by
  intro h
  have := certificate3847
  rw [h.1] at this
  norm_num at this
def C3848 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3848 : C3848.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3848 : ¬ (C3848.det = 0 ∧ ∀ i, C3848.adjugate i i ≠ 0) := by
  intro h
  have := certificate3848
  rw [h.1] at this
  norm_num at this
def C3849 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3849 : C3849.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3849 : ¬ (C3849.det = 0 ∧ ∀ i, C3849.adjugate i i ≠ 0) := by
  intro h
  have := certificate3849
  rw [h.1] at this
  norm_num at this
def C3850 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3850 : C3850.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3850 : ¬ (C3850.det = 0 ∧ ∀ i, C3850.adjugate i i ≠ 0) := by
  intro h
  have := certificate3850
  rw [h.1] at this
  norm_num at this
def C3851 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3851 : C3851.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3851 : ¬ (C3851.det = 0 ∧ ∀ i, C3851.adjugate i i ≠ 0) := by
  intro h
  have := certificate3851
  rw [h.1] at this
  norm_num at this
def C3852 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3852 : C3852.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3852 : ¬ (C3852.det = 0 ∧ ∀ i, C3852.adjugate i i ≠ 0) := by
  intro h
  have := certificate3852
  rw [h.1] at this
  norm_num at this
def C3853 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3853 : C3853.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3853 : ¬ (C3853.det = 0 ∧ ∀ i, C3853.adjugate i i ≠ 0) := by
  intro h
  have := certificate3853
  rw [h.1] at this
  norm_num at this
def C3854 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3854 : C3854.det = (-39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3854 : ¬ (C3854.det = 0 ∧ ∀ i, C3854.adjugate i i ≠ 0) := by
  intro h
  have := certificate3854
  rw [h.1] at this
  norm_num at this
def C3855 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3855 : C3855.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3855 : ¬ (C3855.det = 0 ∧ ∀ i, C3855.adjugate i i ≠ 0) := by
  intro h
  have := certificate3855
  rw [h.1] at this
  norm_num at this
def C3856 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3856 : C3856.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3856 : ¬ (C3856.det = 0 ∧ ∀ i, C3856.adjugate i i ≠ 0) := by
  intro h
  have := certificate3856
  rw [h.1] at this
  norm_num at this
def C3857 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3857 : C3857.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3857 : ¬ (C3857.det = 0 ∧ ∀ i, C3857.adjugate i i ≠ 0) := by
  intro h
  have := certificate3857
  rw [h.1] at this
  norm_num at this
def C3858 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3858 : C3858.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3858 : ¬ (C3858.det = 0 ∧ ∀ i, C3858.adjugate i i ≠ 0) := by
  intro h
  have := certificate3858
  rw [h.1] at this
  norm_num at this
def C3859 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3859 : C3859.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3859 : ¬ (C3859.det = 0 ∧ ∀ i, C3859.adjugate i i ≠ 0) := by
  intro h
  have := certificate3859
  rw [h.1] at this
  norm_num at this
def C3860 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3860 : C3860.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3860 : ¬ (C3860.det = 0 ∧ ∀ i, C3860.adjugate i i ≠ 0) := by
  intro h
  have := certificate3860
  rw [h.1] at this
  norm_num at this
def C3861 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3861 : C3861.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3861 : ¬ (C3861.det = 0 ∧ ∀ i, C3861.adjugate i i ≠ 0) := by
  intro h
  have := certificate3861
  rw [h.1] at this
  norm_num at this
def C3862 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3862 : C3862.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3862 : ¬ (C3862.det = 0 ∧ ∀ i, C3862.adjugate i i ≠ 0) := by
  intro h
  have := certificate3862
  rw [h.1] at this
  norm_num at this
def C3863 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3863 : C3863.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3863 : ¬ (C3863.det = 0 ∧ ∀ i, C3863.adjugate i i ≠ 0) := by
  intro h
  have := certificate3863
  rw [h.1] at this
  norm_num at this
def C3864 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3864 : C3864.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3864 : ¬ (C3864.det = 0 ∧ ∀ i, C3864.adjugate i i ≠ 0) := by
  intro h
  have := certificate3864
  rw [h.1] at this
  norm_num at this
def C3865 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3865 : C3865.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3865 : ¬ (C3865.det = 0 ∧ ∀ i, C3865.adjugate i i ≠ 0) := by
  intro h
  have := certificate3865
  rw [h.1] at this
  norm_num at this
def C3866 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3866 : C3866.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3866 : ¬ (C3866.det = 0 ∧ ∀ i, C3866.adjugate i i ≠ 0) := by
  intro h
  have := certificate3866
  rw [h.1] at this
  norm_num at this
def C3867 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3867 : C3867.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3867 : ¬ (C3867.det = 0 ∧ ∀ i, C3867.adjugate i i ≠ 0) := by
  intro h
  have := certificate3867
  rw [h.1] at this
  norm_num at this
def C3868 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3868 : C3868.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3868 : ¬ (C3868.det = 0 ∧ ∀ i, C3868.adjugate i i ≠ 0) := by
  intro h
  have := certificate3868
  rw [h.1] at this
  norm_num at this
def C3869 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate3869 : C3869.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3869 : ¬ (C3869.det = 0 ∧ ∀ i, C3869.adjugate i i ≠ 0) := by
  intro h
  have := certificate3869
  rw [h.1] at this
  norm_num at this
def C3870 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3870 : C3870.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3870 : ¬ (C3870.det = 0 ∧ ∀ i, C3870.adjugate i i ≠ 0) := by
  intro h
  have := certificate3870
  rw [h.1] at this
  norm_num at this
def C3871 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3871 : C3871.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3871 : ¬ (C3871.det = 0 ∧ ∀ i, C3871.adjugate i i ≠ 0) := by
  intro h
  have := certificate3871
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0120
