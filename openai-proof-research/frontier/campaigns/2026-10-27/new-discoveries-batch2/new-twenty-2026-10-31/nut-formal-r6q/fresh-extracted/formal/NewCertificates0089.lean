import VerifiedDet
namespace Nut8.NewCertificates0089
def C2848 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2848 : C2848.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2848 : ¬ (C2848.det = 0 ∧ ∀ i, C2848.adjugate i i ≠ 0) := by
  intro h
  have := certificate2848
  rw [h.1] at this
  norm_num at this
def C2849 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2849 : C2849.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2849 : ¬ (C2849.det = 0 ∧ ∀ i, C2849.adjugate i i ≠ 0) := by
  intro h
  have := certificate2849
  rw [h.1] at this
  norm_num at this
def C2850 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2850 : C2850.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2850 : ¬ (C2850.det = 0 ∧ ∀ i, C2850.adjugate i i ≠ 0) := by
  intro h
  have := certificate2850
  rw [h.1] at this
  norm_num at this
def C2851 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2851 : C2851.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2851 : ¬ (C2851.det = 0 ∧ ∀ i, C2851.adjugate i i ≠ 0) := by
  intro h
  have := certificate2851
  rw [h.1] at this
  norm_num at this
def C2852 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2852 : C2852.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2852 : ¬ (C2852.det = 0 ∧ ∀ i, C2852.adjugate i i ≠ 0) := by
  intro h
  have := certificate2852
  rw [h.1] at this
  norm_num at this
def C2853 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2853 : C2853.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2853 : ¬ (C2853.det = 0 ∧ ∀ i, C2853.adjugate i i ≠ 0) := by
  intro h
  have := certificate2853
  rw [h.1] at this
  norm_num at this
def C2854 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2854 : C2854.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2854 : ¬ (C2854.det = 0 ∧ ∀ i, C2854.adjugate i i ≠ 0) := by
  intro h
  have := certificate2854
  rw [h.1] at this
  norm_num at this
def C2855 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2855 : C2855.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2855 : ¬ (C2855.det = 0 ∧ ∀ i, C2855.adjugate i i ≠ 0) := by
  intro h
  have := certificate2855
  rw [h.1] at this
  norm_num at this
def C2856 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2856 : C2856.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2856 : ¬ (C2856.det = 0 ∧ ∀ i, C2856.adjugate i i ≠ 0) := by
  intro h
  have := certificate2856
  rw [h.1] at this
  norm_num at this
def C2857 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2857 : C2857.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2857 : ¬ (C2857.det = 0 ∧ ∀ i, C2857.adjugate i i ≠ 0) := by
  intro h
  have := certificate2857
  rw [h.1] at this
  norm_num at this
def C2858 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2858 : C2858.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2858 : ¬ (C2858.det = 0 ∧ ∀ i, C2858.adjugate i i ≠ 0) := by
  intro h
  have := certificate2858
  rw [h.1] at this
  norm_num at this
def C2859 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2859 : C2859.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2859 : ¬ (C2859.det = 0 ∧ ∀ i, C2859.adjugate i i ≠ 0) := by
  intro h
  have := certificate2859
  rw [h.1] at this
  norm_num at this
def C2860 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2860 : C2860.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2860 : ¬ (C2860.det = 0 ∧ ∀ i, C2860.adjugate i i ≠ 0) := by
  intro h
  have := certificate2860
  rw [h.1] at this
  norm_num at this
def C2861 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2861 : C2861.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2861 : ¬ (C2861.det = 0 ∧ ∀ i, C2861.adjugate i i ≠ 0) := by
  intro h
  have := certificate2861
  rw [h.1] at this
  norm_num at this
def C2862 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2862 : C2862.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2862 : ¬ (C2862.det = 0 ∧ ∀ i, C2862.adjugate i i ≠ 0) := by
  intro h
  have := certificate2862
  rw [h.1] at this
  norm_num at this
def C2863 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2863 : C2863.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2863 : ¬ (C2863.det = 0 ∧ ∀ i, C2863.adjugate i i ≠ 0) := by
  intro h
  have := certificate2863
  rw [h.1] at this
  norm_num at this
def C2864 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2864 : C2864.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2864 : ¬ (C2864.det = 0 ∧ ∀ i, C2864.adjugate i i ≠ 0) := by
  intro h
  have := certificate2864
  rw [h.1] at this
  norm_num at this
def C2865 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2865 : C2865.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2865 : ¬ (C2865.det = 0 ∧ ∀ i, C2865.adjugate i i ≠ 0) := by
  intro h
  have := certificate2865
  rw [h.1] at this
  norm_num at this
def C2866 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2866 : C2866.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2866 : ¬ (C2866.det = 0 ∧ ∀ i, C2866.adjugate i i ≠ 0) := by
  intro h
  have := certificate2866
  rw [h.1] at this
  norm_num at this
def C2867 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2867 : C2867.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2867 : ¬ (C2867.det = 0 ∧ ∀ i, C2867.adjugate i i ≠ 0) := by
  intro h
  have := certificate2867
  rw [h.1] at this
  norm_num at this
def C2868 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2868 : C2868.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2868 : ¬ (C2868.det = 0 ∧ ∀ i, C2868.adjugate i i ≠ 0) := by
  intro h
  have := certificate2868
  rw [h.1] at this
  norm_num at this
def C2869 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2869 : C2869.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2869 : ¬ (C2869.det = 0 ∧ ∀ i, C2869.adjugate i i ≠ 0) := by
  intro h
  have := certificate2869
  rw [h.1] at this
  norm_num at this
def C2870 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2870 : C2870.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2870 : ¬ (C2870.det = 0 ∧ ∀ i, C2870.adjugate i i ≠ 0) := by
  intro h
  have := certificate2870
  rw [h.1] at this
  norm_num at this
def C2871 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2871 : C2871.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2871 : ¬ (C2871.det = 0 ∧ ∀ i, C2871.adjugate i i ≠ 0) := by
  intro h
  have := certificate2871
  rw [h.1] at this
  norm_num at this
def C2872 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2872 : C2872.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2872 : ¬ (C2872.det = 0 ∧ ∀ i, C2872.adjugate i i ≠ 0) := by
  intro h
  have := certificate2872
  rw [h.1] at this
  norm_num at this
def C2873 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2873 : C2873.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2873 : ¬ (C2873.det = 0 ∧ ∀ i, C2873.adjugate i i ≠ 0) := by
  intro h
  have := certificate2873
  rw [h.1] at this
  norm_num at this
def C2874 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2874 : C2874.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2874 : ¬ (C2874.det = 0 ∧ ∀ i, C2874.adjugate i i ≠ 0) := by
  intro h
  have := certificate2874
  rw [h.1] at this
  norm_num at this
def C2875 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2875 : C2875.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2875 : ¬ (C2875.det = 0 ∧ ∀ i, C2875.adjugate i i ≠ 0) := by
  intro h
  have := certificate2875
  rw [h.1] at this
  norm_num at this
def C2876 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2876 : C2876.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2876 : ¬ (C2876.det = 0 ∧ ∀ i, C2876.adjugate i i ≠ 0) := by
  intro h
  have := certificate2876
  rw [h.1] at this
  norm_num at this
def C2877 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2877 : C2877.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2877 : ¬ (C2877.det = 0 ∧ ∀ i, C2877.adjugate i i ≠ 0) := by
  intro h
  have := certificate2877
  rw [h.1] at this
  norm_num at this
def C2878 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2878 : C2878.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2878 : ¬ (C2878.det = 0 ∧ ∀ i, C2878.adjugate i i ≠ 0) := by
  intro h
  have := certificate2878
  rw [h.1] at this
  norm_num at this
def C2879 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2879 : C2879.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2879 : ¬ (C2879.det = 0 ∧ ∀ i, C2879.adjugate i i ≠ 0) := by
  intro h
  have := certificate2879
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0089
