import VerifiedDet
namespace Nut8.NewCertificates0087
def C2784 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2784 : C2784.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2784 : ¬ (C2784.det = 0 ∧ ∀ i, C2784.adjugate i i ≠ 0) := by
  intro h
  have := certificate2784
  rw [h.1] at this
  norm_num at this
def C2785 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2785 : C2785.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2785 : ¬ (C2785.det = 0 ∧ ∀ i, C2785.adjugate i i ≠ 0) := by
  intro h
  have := certificate2785
  rw [h.1] at this
  norm_num at this
def C2786 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2786 : C2786.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2786 : ¬ (C2786.det = 0 ∧ ∀ i, C2786.adjugate i i ≠ 0) := by
  intro h
  have := certificate2786
  rw [h.1] at this
  norm_num at this
def C2787 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2787 : C2787.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2787 : ¬ (C2787.det = 0 ∧ ∀ i, C2787.adjugate i i ≠ 0) := by
  intro h
  have := certificate2787
  rw [h.1] at this
  norm_num at this
def C2788 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2788 : C2788.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2788 : ¬ (C2788.det = 0 ∧ ∀ i, C2788.adjugate i i ≠ 0) := by
  intro h
  have := certificate2788
  rw [h.1] at this
  norm_num at this
def C2789 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2789 : C2789.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2789 : ¬ (C2789.det = 0 ∧ ∀ i, C2789.adjugate i i ≠ 0) := by
  intro h
  have := certificate2789
  rw [h.1] at this
  norm_num at this
def C2790 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2790 : C2790.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2790 : ¬ (C2790.det = 0 ∧ ∀ i, C2790.adjugate i i ≠ 0) := by
  intro h
  have := certificate2790
  rw [h.1] at this
  norm_num at this
def C2791 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2791 : C2791.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2791 : ¬ (C2791.det = 0 ∧ ∀ i, C2791.adjugate i i ≠ 0) := by
  intro h
  have := certificate2791
  rw [h.1] at this
  norm_num at this
def C2792 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2792 : C2792.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2792 : ¬ (C2792.det = 0 ∧ ∀ i, C2792.adjugate i i ≠ 0) := by
  intro h
  have := certificate2792
  rw [h.1] at this
  norm_num at this
def C2793 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2793 : C2793.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2793 : ¬ (C2793.det = 0 ∧ ∀ i, C2793.adjugate i i ≠ 0) := by
  intro h
  have := certificate2793
  rw [h.1] at this
  norm_num at this
def C2794 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2794 : C2794.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2794 : ¬ (C2794.det = 0 ∧ ∀ i, C2794.adjugate i i ≠ 0) := by
  intro h
  have := certificate2794
  rw [h.1] at this
  norm_num at this
def C2795 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2795 : C2795.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2795 : ¬ (C2795.det = 0 ∧ ∀ i, C2795.adjugate i i ≠ 0) := by
  intro h
  have := certificate2795
  rw [h.1] at this
  norm_num at this
def C2796 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2796 : C2796.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2796 : ¬ (C2796.det = 0 ∧ ∀ i, C2796.adjugate i i ≠ 0) := by
  intro h
  have := certificate2796
  rw [h.1] at this
  norm_num at this
def C2797 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2797 : C2797.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2797 : ¬ (C2797.det = 0 ∧ ∀ i, C2797.adjugate i i ≠ 0) := by
  intro h
  have := certificate2797
  rw [h.1] at this
  norm_num at this
def C2798 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2798 : C2798.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2798 : ¬ (C2798.det = 0 ∧ ∀ i, C2798.adjugate i i ≠ 0) := by
  intro h
  have := certificate2798
  rw [h.1] at this
  norm_num at this
def C2799 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2799 : C2799.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2799 : ¬ (C2799.det = 0 ∧ ∀ i, C2799.adjugate i i ≠ 0) := by
  intro h
  have := certificate2799
  rw [h.1] at this
  norm_num at this
def C2800 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2800 : C2800.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2800 : ¬ (C2800.det = 0 ∧ ∀ i, C2800.adjugate i i ≠ 0) := by
  intro h
  have := certificate2800
  rw [h.1] at this
  norm_num at this
def C2801 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2801 : C2801.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2801 : ¬ (C2801.det = 0 ∧ ∀ i, C2801.adjugate i i ≠ 0) := by
  intro h
  have := certificate2801
  rw [h.1] at this
  norm_num at this
def C2802 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2802 : C2802.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2802 : ¬ (C2802.det = 0 ∧ ∀ i, C2802.adjugate i i ≠ 0) := by
  intro h
  have := certificate2802
  rw [h.1] at this
  norm_num at this
def C2803 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2803 : C2803.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2803 : ¬ (C2803.det = 0 ∧ ∀ i, C2803.adjugate i i ≠ 0) := by
  intro h
  have := certificate2803
  rw [h.1] at this
  norm_num at this
def C2804 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2804 : C2804.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2804 : ¬ (C2804.det = 0 ∧ ∀ i, C2804.adjugate i i ≠ 0) := by
  intro h
  have := certificate2804
  rw [h.1] at this
  norm_num at this
def C2805 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2805 : C2805.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2805 : ¬ (C2805.det = 0 ∧ ∀ i, C2805.adjugate i i ≠ 0) := by
  intro h
  have := certificate2805
  rw [h.1] at this
  norm_num at this
def C2806 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2806 : C2806.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2806 : ¬ (C2806.det = 0 ∧ ∀ i, C2806.adjugate i i ≠ 0) := by
  intro h
  have := certificate2806
  rw [h.1] at this
  norm_num at this
def C2807 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2807 : C2807.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2807 : ¬ (C2807.det = 0 ∧ ∀ i, C2807.adjugate i i ≠ 0) := by
  intro h
  have := certificate2807
  rw [h.1] at this
  norm_num at this
def C2808 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate2808 : C2808.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2808 : ¬ (C2808.det = 0 ∧ ∀ i, C2808.adjugate i i ≠ 0) := by
  intro h
  have := certificate2808
  rw [h.1] at this
  norm_num at this
def C2809 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate2809 : C2809.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2809 : ¬ (C2809.det = 0 ∧ ∀ i, C2809.adjugate i i ≠ 0) := by
  intro h
  have := certificate2809
  rw [h.1] at this
  norm_num at this
def C2810 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2810 : C2810.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2810 : ¬ (C2810.det = 0 ∧ ∀ i, C2810.adjugate i i ≠ 0) := by
  intro h
  have := certificate2810
  rw [h.1] at this
  norm_num at this
def C2811 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2811 : C2811.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2811 : ¬ (C2811.det = 0 ∧ ∀ i, C2811.adjugate i i ≠ 0) := by
  intro h
  have := certificate2811
  rw [h.1] at this
  norm_num at this
def C2812 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate2812 : C2812.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2812 : ¬ (C2812.det = 0 ∧ ∀ i, C2812.adjugate i i ≠ 0) := by
  intro h
  have := certificate2812
  rw [h.1] at this
  norm_num at this
def C2813 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate2813 : C2813.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2813 : ¬ (C2813.det = 0 ∧ ∀ i, C2813.adjugate i i ≠ 0) := by
  intro h
  have := certificate2813
  rw [h.1] at this
  norm_num at this
def C2814 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2814 : C2814.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2814 : ¬ (C2814.det = 0 ∧ ∀ i, C2814.adjugate i i ≠ 0) := by
  intro h
  have := certificate2814
  rw [h.1] at this
  norm_num at this
def C2815 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate2815 : C2815.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2815 : ¬ (C2815.det = 0 ∧ ∀ i, C2815.adjugate i i ≠ 0) := by
  intro h
  have := certificate2815
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0087
