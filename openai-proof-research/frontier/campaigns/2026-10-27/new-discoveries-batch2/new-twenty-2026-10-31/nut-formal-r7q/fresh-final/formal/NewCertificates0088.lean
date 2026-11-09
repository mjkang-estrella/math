import VerifiedDet
namespace Nut8.NewCertificates0088
def C2816 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2816 : C2816.det = (49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2816 : ¬ (C2816.det = 0 ∧ ∀ i, C2816.adjugate i i ≠ 0) := by
  intro h
  have := certificate2816
  rw [h.1] at this
  norm_num at this
def C2817 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2817 : C2817.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2817 : ¬ (C2817.det = 0 ∧ ∀ i, C2817.adjugate i i ≠ 0) := by
  intro h
  have := certificate2817
  rw [h.1] at this
  norm_num at this
def C2818 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2818 : C2818.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2818 : ¬ (C2818.det = 0 ∧ ∀ i, C2818.adjugate i i ≠ 0) := by
  intro h
  have := certificate2818
  rw [h.1] at this
  norm_num at this
def C2819 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2819 : C2819.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2819 : ¬ (C2819.det = 0 ∧ ∀ i, C2819.adjugate i i ≠ 0) := by
  intro h
  have := certificate2819
  rw [h.1] at this
  norm_num at this
def C2820 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2820 : C2820.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2820 : ¬ (C2820.det = 0 ∧ ∀ i, C2820.adjugate i i ≠ 0) := by
  intro h
  have := certificate2820
  rw [h.1] at this
  norm_num at this
def C2821 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2821 : C2821.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2821 : ¬ (C2821.det = 0 ∧ ∀ i, C2821.adjugate i i ≠ 0) := by
  intro h
  have := certificate2821
  rw [h.1] at this
  norm_num at this
def C2822 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2822 : C2822.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2822 : ¬ (C2822.det = 0 ∧ ∀ i, C2822.adjugate i i ≠ 0) := by
  intro h
  have := certificate2822
  rw [h.1] at this
  norm_num at this
def C2823 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2823 : C2823.det = (49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2823 : ¬ (C2823.det = 0 ∧ ∀ i, C2823.adjugate i i ≠ 0) := by
  intro h
  have := certificate2823
  rw [h.1] at this
  norm_num at this
def C2824 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2824 : C2824.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2824 : ¬ (C2824.det = 0 ∧ ∀ i, C2824.adjugate i i ≠ 0) := by
  intro h
  have := certificate2824
  rw [h.1] at this
  norm_num at this
def C2825 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2825 : C2825.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2825 : ¬ (C2825.det = 0 ∧ ∀ i, C2825.adjugate i i ≠ 0) := by
  intro h
  have := certificate2825
  rw [h.1] at this
  norm_num at this
def C2826 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2826 : C2826.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2826 : ¬ (C2826.det = 0 ∧ ∀ i, C2826.adjugate i i ≠ 0) := by
  intro h
  have := certificate2826
  rw [h.1] at this
  norm_num at this
def C2827 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2827 : C2827.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2827 : ¬ (C2827.det = 0 ∧ ∀ i, C2827.adjugate i i ≠ 0) := by
  intro h
  have := certificate2827
  rw [h.1] at this
  norm_num at this
def C2828 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2828 : C2828.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2828 : ¬ (C2828.det = 0 ∧ ∀ i, C2828.adjugate i i ≠ 0) := by
  intro h
  have := certificate2828
  rw [h.1] at this
  norm_num at this
def C2829 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate2829 : C2829.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2829 : ¬ (C2829.det = 0 ∧ ∀ i, C2829.adjugate i i ≠ 0) := by
  intro h
  have := certificate2829
  rw [h.1] at this
  norm_num at this
def C2830 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2830 : C2830.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2830 : ¬ (C2830.det = 0 ∧ ∀ i, C2830.adjugate i i ≠ 0) := by
  intro h
  have := certificate2830
  rw [h.1] at this
  norm_num at this
def C2831 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2831 : C2831.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2831 : ¬ (C2831.det = 0 ∧ ∀ i, C2831.adjugate i i ≠ 0) := by
  intro h
  have := certificate2831
  rw [h.1] at this
  norm_num at this
def C2832 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2832 : C2832.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2832 : ¬ (C2832.det = 0 ∧ ∀ i, C2832.adjugate i i ≠ 0) := by
  intro h
  have := certificate2832
  rw [h.1] at this
  norm_num at this
def C2833 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2833 : C2833.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2833 : ¬ (C2833.det = 0 ∧ ∀ i, C2833.adjugate i i ≠ 0) := by
  intro h
  have := certificate2833
  rw [h.1] at this
  norm_num at this
def C2834 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2834 : C2834.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2834 : ¬ (C2834.det = 0 ∧ ∀ i, C2834.adjugate i i ≠ 0) := by
  intro h
  have := certificate2834
  rw [h.1] at this
  norm_num at this
def C2835 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2835 : C2835.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2835 : ¬ (C2835.det = 0 ∧ ∀ i, C2835.adjugate i i ≠ 0) := by
  intro h
  have := certificate2835
  rw [h.1] at this
  norm_num at this
def C2836 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2836 : C2836.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2836 : ¬ (C2836.det = 0 ∧ ∀ i, C2836.adjugate i i ≠ 0) := by
  intro h
  have := certificate2836
  rw [h.1] at this
  norm_num at this
def C2837 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2837 : C2837.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2837 : ¬ (C2837.det = 0 ∧ ∀ i, C2837.adjugate i i ≠ 0) := by
  intro h
  have := certificate2837
  rw [h.1] at this
  norm_num at this
def C2838 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2838 : C2838.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2838 : ¬ (C2838.det = 0 ∧ ∀ i, C2838.adjugate i i ≠ 0) := by
  intro h
  have := certificate2838
  rw [h.1] at this
  norm_num at this
def C2839 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2839 : C2839.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2839 : ¬ (C2839.det = 0 ∧ ∀ i, C2839.adjugate i i ≠ 0) := by
  intro h
  have := certificate2839
  rw [h.1] at this
  norm_num at this
def C2840 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2840 : C2840.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2840 : ¬ (C2840.det = 0 ∧ ∀ i, C2840.adjugate i i ≠ 0) := by
  intro h
  have := certificate2840
  rw [h.1] at this
  norm_num at this
def C2841 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2841 : C2841.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2841 : ¬ (C2841.det = 0 ∧ ∀ i, C2841.adjugate i i ≠ 0) := by
  intro h
  have := certificate2841
  rw [h.1] at this
  norm_num at this
def C2842 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2842 : C2842.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2842 : ¬ (C2842.det = 0 ∧ ∀ i, C2842.adjugate i i ≠ 0) := by
  intro h
  have := certificate2842
  rw [h.1] at this
  norm_num at this
def C2843 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2843 : C2843.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2843 : ¬ (C2843.det = 0 ∧ ∀ i, C2843.adjugate i i ≠ 0) := by
  intro h
  have := certificate2843
  rw [h.1] at this
  norm_num at this
def C2844 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2844 : C2844.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2844 : ¬ (C2844.det = 0 ∧ ∀ i, C2844.adjugate i i ≠ 0) := by
  intro h
  have := certificate2844
  rw [h.1] at this
  norm_num at this
def C2845 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2845 : C2845.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2845 : ¬ (C2845.det = 0 ∧ ∀ i, C2845.adjugate i i ≠ 0) := by
  intro h
  have := certificate2845
  rw [h.1] at this
  norm_num at this
def C2846 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2846 : C2846.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2846 : ¬ (C2846.det = 0 ∧ ∀ i, C2846.adjugate i i ≠ 0) := by
  intro h
  have := certificate2846
  rw [h.1] at this
  norm_num at this
def C2847 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2847 : C2847.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2847 : ¬ (C2847.det = 0 ∧ ∀ i, C2847.adjugate i i ≠ 0) := by
  intro h
  have := certificate2847
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0088
